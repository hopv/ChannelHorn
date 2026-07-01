use anyhow::Result;
use std::collections::HashMap;

use crate::{
    chc::{
        Body, CHC, Clause, Constraint, Datatype, DatatypeVariant, DisjunctiveBody, PredicateAtom,
        PredicateName, Setting, Term, Type,
    },
    core::ast::{self},
};

static CLOSED_PREDICATE: &str = "%Closed";

#[derive(Debug, Default)]
pub struct Ctx {
    var_declarations: HashMap<PredicateName, Type>,
    fun_declarations: HashMap<PredicateName, Vec<Type>>,
    type_env: HashMap<ast::VarName, ast::Type>,
    adts: HashMap<ast::TypeName, ast::AdtDef>,
    primitive_payload_types: Vec<Type>,
    closed_payload_types: Vec<ast::Type>,
    closed_value_types: Vec<ast::Type>,
    unused_num: usize,
    setting: Setting,
}

impl Ctx {
    fn insert_declared_var(&mut self, name: impl Into<PredicateName>, ty: Type) -> Result<Term> {
        let name = name.into();
        if let Some(existing_ty) = self.var_declarations.get(&name) {
            if existing_ty != &ty {
                anyhow::bail!("Variable {} already declared with a different type", name);
            }
        } else {
            self.var_declarations.insert(name.clone(), ty);
        }
        Ok(Term::Var(name))
    }

    fn separate_type_env(
        &mut self,
        first_fun_call: &ast::FuncCall,
    ) -> Result<HashMap<ast::VarName, ast::Type>> {
        let mut after_type_env = self.type_env.clone();
        std::mem::swap(&mut self.type_env, &mut after_type_env);
        let free_vars = first_fun_call.free_vars();
        for var in free_vars {
            if let Some(ty) = after_type_env.get(&var) {
                let ty = ty.clone();
                if ty.is_linear() {
                    after_type_env.remove(&var);
                }
                self.type_env.insert(var, ty);
            } else {
                anyhow::bail!("Variable {} not found in type environment", var);
            }
        }
        Ok(after_type_env)
    }

    fn insert_to_type_env(&mut self, var: impl Into<ast::VarName>, ty: ast::Type) -> Result<()> {
        let var = var.into();
        if let Some(existing_ty) = self.type_env.get(&var) {
            if existing_ty != &ty {
                anyhow::bail!("Variable {} already declared with a different type", var);
            }
        } else {
            self.type_env.insert(var, ty);
        }
        Ok(())
    }

    fn get_ast_type(&self, var: &ast::VarName) -> Result<&ast::Type> {
        self.type_env
            .get(var)
            .ok_or_else(|| anyhow::anyhow!("Variable {} not found in type environment", var))
    }

    fn collect_linear_vars(&self) -> Vec<(ast::VarName, ast::Type)> {
        self.type_env
            .iter()
            .filter_map(|(var, ty)| {
                if ty.is_linear() {
                    Some((var.clone(), ty.clone()))
                } else {
                    None
                }
            })
            .collect()
    }

    fn gen_new_var(&mut self, previous_var: &str) -> ast::VarName {
        let previous_var = previous_var.trim_end_matches('%');
        let var_name = format!("{}%{}", previous_var, self.unused_num);
        self.unused_num += 1;
        var_name
    }

    fn ensure_primitive_payload(&mut self, payload_ty: Type) {
        if !self.primitive_payload_types.contains(&payload_ty) {
            self.primitive_payload_types.push(payload_ty.clone());
        }
        self.fun_declarations
            .extend(CHC::primitive_fun_declarations(&self.setting, payload_ty));
    }

    fn primitive_predicates_for_payload(
        &mut self,
        payload_ty: Type,
    ) -> (PredicateName, PredicateName) {
        self.ensure_primitive_payload(payload_ty.clone());
        CHC::primitive_predicate_names(&payload_ty)
    }

    fn ensure_closed_payload(&mut self, payload: ast::Type) -> Result<PredicateName> {
        let name = closed_predicate_name(&payload);
        if !self.closed_payload_types.contains(&payload) {
            let predicate_ty = closed_list_type(&payload, &self.setting)?;
            self.closed_payload_types.push(payload.clone());
            self.fun_declarations
                .insert(name.clone(), vec![predicate_ty]);
            if let ast::Type::Receiver(inner) = &payload {
                if needs_closed_value(inner) {
                    self.ensure_closed_payload((**inner).clone())?;
                }
            }
        }
        Ok(name)
    }

    fn add_closed_value_conditions(
        &mut self,
        body: &mut Body,
        term: Term,
        ty: &ast::Type,
    ) -> Result<()> {
        match ty {
            ast::Type::Sender(_) => {
                body.constraints.push(Constraint::Eq(
                    term,
                    Term::Nil(ty.lower_to_chc(&self.setting)?),
                ));
            }
            ast::Type::Receiver(payload) if needs_closed_value(payload) => {
                let name = self.ensure_closed_payload((**payload).clone())?;
                body.predicates.push(PredicateAtom {
                    name,
                    args: vec![term],
                });
            }
            ast::Type::Adt(_) => {
                let name = self.ensure_closed_adt_value(ty.clone())?;
                body.predicates.push(PredicateAtom {
                    name,
                    args: vec![term],
                });
            }
            ast::Type::Int | ast::Type::Func { .. } | ast::Type::Receiver(_) => {}
        }
        Ok(())
    }

    fn ensure_closed_adt_value(&mut self, ty: ast::Type) -> Result<PredicateName> {
        let name = closed_value_predicate_name(&ty);
        if !self.closed_value_types.contains(&ty) {
            let chc_ty = ty.lower_to_chc(&self.setting)?;
            self.closed_value_types.push(ty.clone());
            self.fun_declarations.insert(name.clone(), vec![chc_ty]);
            if let ast::Type::Adt(type_name) = &ty {
                let adt = self
                    .adts
                    .get(type_name)
                    .ok_or_else(|| anyhow::anyhow!("unknown ADT type {}", type_name))?
                    .clone();
                for variant in &adt.variants {
                    for field in &variant.fields {
                        match field {
                            ast::Type::Receiver(payload) if needs_closed_value(payload) => {
                                self.ensure_closed_payload((**payload).clone())?;
                            }
                            ast::Type::Adt(_) => {
                                self.ensure_closed_adt_value(field.clone())?;
                            }
                            _ => {}
                        }
                    }
                }
            }
        }
        Ok(name)
    }

    fn terminal_closed_body(&mut self) -> Result<Body> {
        let mut body = Body::default();
        for (var, ty) in self.collect_linear_vars() {
            let term = self.insert_declared_var(var, ty.lower_to_chc(&self.setting)?)?;
            self.add_closed_value_conditions(&mut body, term, &ty)?;
        }
        Ok(body)
    }

    fn closed_clauses_for_payload(&mut self, payload: &ast::Type) -> Result<Vec<Clause>> {
        let predicate_name = closed_predicate_name(payload);
        let list_ty = closed_list_type(payload, &self.setting)?;
        let payload_ty = payload.lower_to_chc(&self.setting)?;
        let item_ty = if self.setting.no_timestamps {
            payload_ty
        } else {
            Type::timestamped_value(payload_ty)
        };
        let value_term = if self.setting.no_timestamps {
            Term::Var("p".to_string())
        } else {
            Term::Val(Term::Var("p".to_string()).into())
        };
        let mut recursive_body = Body {
            predicates: vec![PredicateAtom {
                name: predicate_name.clone(),
                args: vec![Term::Var("tail".to_string())],
            }],
            constraints: vec![Constraint::Eq(
                Term::Var("l".to_string()),
                Term::Cons(
                    Term::Var("p".to_string()).into(),
                    Term::Var("tail".to_string()).into(),
                ),
            )],
        };
        self.add_closed_value_conditions(&mut recursive_body, value_term, payload)?;

        Ok(vec![
            Clause {
                forall: vec![],
                head: Some(PredicateAtom {
                    name: predicate_name.clone(),
                    args: vec![Term::Nil(list_ty.clone())],
                }),
                body: Body::default(),
            },
            Clause {
                forall: vec![
                    ("l".to_string(), list_ty.clone()),
                    ("p".to_string(), item_ty),
                    ("tail".to_string(), list_ty),
                ],
                head: Some(PredicateAtom {
                    name: predicate_name,
                    args: vec![Term::Var("l".to_string())],
                }),
                body: recursive_body,
            },
        ])
    }

    fn closed_clauses_for_adt_value(&mut self, ty: &ast::Type) -> Result<Vec<Clause>> {
        let ast::Type::Adt(type_name) = ty else {
            return Ok(vec![]);
        };
        let predicate_name = closed_value_predicate_name(ty);
        let adt = self
            .adts
            .get(type_name)
            .ok_or_else(|| anyhow::anyhow!("unknown ADT type {}", type_name))?
            .clone();
        let value_ty = ty.lower_to_chc(&self.setting)?;
        let mut clauses = vec![];
        for variant in &adt.variants {
            let field_terms = variant
                .fields
                .iter()
                .enumerate()
                .map(|(index, _)| Term::Var(format!("field{}", index)))
                .collect::<Vec<_>>();
            let mut body = Body {
                predicates: vec![],
                constraints: vec![Constraint::Eq(
                    Term::Var("v".to_string()),
                    Term::Ctor {
                        name: adt_constructor_name(type_name, &variant.name),
                        args: field_terms.clone(),
                    },
                )],
            };
            for (term, field_ty) in field_terms.iter().cloned().zip(&variant.fields) {
                self.add_closed_value_conditions(&mut body, term, field_ty)?;
            }
            let mut forall = vec![("v".to_string(), value_ty.clone())];
            for (index, field_ty) in variant.fields.iter().enumerate() {
                forall.push((
                    format!("field{}", index),
                    field_ty.lower_to_chc(&self.setting)?,
                ));
            }
            clauses.push(Clause {
                forall,
                head: Some(PredicateAtom {
                    name: predicate_name.clone(),
                    args: vec![Term::Var("v".to_string())],
                }),
                body,
            });
        }
        Ok(clauses)
    }
}

fn ast_type_suffix(ty: &ast::Type) -> String {
    match ty {
        ast::Type::Int => "Int".to_string(),
        ast::Type::Adt(name) => format!("Adt_{}", name),
        ast::Type::Sender(payload) => format!("Sender_{}", ast_type_suffix(payload)),
        ast::Type::Receiver(payload) => format!("Receiver_{}", ast_type_suffix(payload)),
        ast::Type::Func { params } => {
            let params = params
                .iter()
                .map(ast_type_suffix)
                .collect::<Vec<_>>()
                .join("_");
            format!("Func_{}", params)
        }
    }
}

fn closed_predicate_name(payload: &ast::Type) -> PredicateName {
    format!("{}${}", CLOSED_PREDICATE, ast_type_suffix(payload))
}

fn closed_value_predicate_name(ty: &ast::Type) -> PredicateName {
    format!("{}Value${}", CLOSED_PREDICATE, ast_type_suffix(ty))
}

fn needs_closed_value(ty: &ast::Type) -> bool {
    match ty {
        ast::Type::Sender(_) => true,
        ast::Type::Receiver(payload) => needs_closed_value(payload),
        ast::Type::Adt(_) => true,
        ast::Type::Int | ast::Type::Func { .. } => false,
    }
}

fn closed_list_type(payload: &ast::Type, setting: &Setting) -> Result<Type> {
    Ok(Type::prophecy(
        setting.no_timestamps,
        payload.lower_to_chc(setting)?,
    ))
}

fn adt_type_name(name: &str) -> String {
    format!("Adt${}", name)
}

fn adt_constructor_name(type_name: &str, variant: &str) -> String {
    format!("Adt${}${}", type_name, variant)
}

fn adt_selector_name(type_name: &str, variant: &str, index: usize) -> String {
    format!("Adt${}${}${}", type_name, variant, index)
}

fn lower_datatype_def(adt: &ast::AdtDef, setting: &Setting) -> Result<Datatype> {
    let variants = adt
        .variants
        .iter()
        .map(|variant| {
            let fields = variant
                .fields
                .iter()
                .enumerate()
                .map(|(index, ty)| {
                    Ok((
                        adt_selector_name(&adt.name, &variant.name, index),
                        ty.lower_to_chc(setting)?,
                    ))
                })
                .collect::<Result<Vec<_>>>()?;
            Ok(DatatypeVariant {
                name: adt_constructor_name(&adt.name, &variant.name),
                fields,
            })
        })
        .collect::<Result<Vec<_>>>()?;
    Ok(Datatype {
        name: adt_type_name(&adt.name),
        variants,
    })
}

#[derive(Debug)]
pub struct LocalCtx {
    pub error_var: Term,
    pub time_var: Term,
}

impl ast::Type {
    fn lower_to_chc(&self, setting: &Setting) -> Result<Type> {
        Ok(match self {
            ast::Type::Int => Type::Int,
            ast::Type::Adt(name) => Type::Adt(adt_type_name(name)),
            ast::Type::Sender(payload) | ast::Type::Receiver(payload) => {
                Type::prophecy(setting.no_timestamps, payload.lower_to_chc(setting)?)
            }
            ast::Type::Func { params } => {
                let chc_params = params
                    .iter()
                    .map(|p| p.lower_to_chc(setting))
                    .collect::<Result<Vec<_>>>()?;
                Type::Func { args: chc_params }
            }
        })
    }
}

impl ast::Expr {
    fn lower_to_chc(&self, ctx: &mut Ctx) -> Result<Term> {
        Ok(match self {
            ast::Expr::Num(n) => Term::Int(*n),
            ast::Expr::Var(var) => {
                let ast_ty = ctx.get_ast_type(var)?.clone();
                let chc_ty = ast_ty.lower_to_chc(&ctx.setting)?;
                ctx.insert_declared_var(var.clone(), chc_ty)?
            }
            ast::Expr::Ctor {
                type_name,
                variant,
                args,
            } => {
                let args = args
                    .iter()
                    .map(|arg| arg.lower_to_chc(ctx))
                    .collect::<Result<Vec<_>>>()?;
                Term::Ctor {
                    name: adt_constructor_name(type_name, variant),
                    args,
                }
            }
            ast::Expr::Op(expr1, op_kind, expr2) => {
                let term1 = expr1.lower_to_chc(ctx)?;
                let term2 = expr2.lower_to_chc(ctx)?;
                match op_kind {
                    ast::OpKind::Add => Term::Add(Box::new(term1), Box::new(term2)),
                    ast::OpKind::Sub => Term::Sub(Box::new(term1), Box::new(term2)),
                    ast::OpKind::Mul => Term::Mul(Box::new(term1), Box::new(term2)),
                    ast::OpKind::Eq => Term::Eq(Box::new(term1), Box::new(term2)),
                    ast::OpKind::Ne => Term::Ne(Box::new(term1), Box::new(term2)),
                    ast::OpKind::Lt => Term::Lt(Box::new(term1), Box::new(term2)),
                    ast::OpKind::Le => Term::Le(Box::new(term1), Box::new(term2)),
                    ast::OpKind::Gt => Term::Gt(Box::new(term1), Box::new(term2)),
                    ast::OpKind::Ge => Term::Ge(Box::new(term1), Box::new(term2)),
                }
            }
        })
    }
}

static DEFAULT_ERROR_VAR: &str = "%b";
static DEFAULT_TIME_VAR: &str = "%t";

impl ast::FuncCall {
    fn lower_to_chc(&self, ctx: &mut Ctx, lctx: &LocalCtx) -> Result<Body> {
        let ast::FuncCall { name, args } = self;
        let error_var = lctx.error_var.clone();
        let time_var = lctx.time_var.clone();
        let default_args = if ctx.setting.no_timestamps {
            vec![error_var]
        } else {
            vec![error_var, time_var]
        };
        let args_term = args
            .iter()
            .map(|arg| arg.lower_to_chc(ctx))
            .collect::<Result<Vec<_>>>()?;
        Ok(Body {
            predicates: vec![PredicateAtom {
                name: name.clone(),
                args: default_args.into_iter().chain(args_term).collect(),
            }],
            constraints: vec![],
        })
    }
}

impl ast::Statement {
    fn lower_to_chc(&self, ctx: &mut Ctx, lctx: &LocalCtx) -> Result<DisjunctiveBody> {
        Ok(match self {
            ast::Statement::Unit => {
                if ctx.setting.is_deadlock_mode() {
                    let mut body = ctx.terminal_closed_body()?;
                    body.constraints.push(Constraint::Eq(
                        lctx.error_var.clone(),
                        ctx.setting.terminated_status(),
                    ));
                    vec![body]
                } else {
                    vec![]
                }
            }

            ast::Statement::Fail => {
                let mut body = ctx.terminal_closed_body()?;
                let error_var = lctx.error_var.clone();
                body.constraints
                    .push(Constraint::Eq(error_var, ctx.setting.failure_status()));
                vec![body]
            }
            ast::Statement::Call(func_call) => {
                vec![func_call.lower_to_chc(ctx, lctx)?]
            }
            ast::Statement::If(expr, func_call, func_call1) => {
                let cond_term = expr.lower_to_chc(ctx)?;
                let then_body = func_call.lower_to_chc(ctx, lctx)?;
                let else_body = func_call1.clone().lower_to_chc(ctx, lctx)?;
                vec![
                    Body {
                        predicates: vec![],
                        constraints: vec![Constraint::Ne(cond_term.clone(), Term::Int(0))],
                    }
                    .concat(then_body),
                    Body {
                        predicates: vec![],
                        constraints: vec![Constraint::Eq(cond_term, Term::Int(0))],
                    }
                    .concat(else_body),
                ]
            }
            ast::Statement::Spawn(func_call, func_call1) => {
                let after_type_env = ctx.separate_type_env(func_call)?;
                let first_error_var = ctx.gen_new_var(DEFAULT_ERROR_VAR);
                let first_error_term =
                    ctx.insert_declared_var(&first_error_var, ctx.setting.status_type())?;
                let second_error_var = ctx.gen_new_var(DEFAULT_ERROR_VAR);
                let second_error_term =
                    ctx.insert_declared_var(&second_error_var, ctx.setting.status_type())?;

                let func_call_body = func_call.lower_to_chc(
                    ctx,
                    &LocalCtx {
                        error_var: first_error_term.clone(),
                        time_var: lctx.time_var.clone(),
                    },
                )?;

                let tmp_type_env = std::mem::take(&mut ctx.type_env);

                let func_call1_body = {
                    ctx.type_env = after_type_env;
                    func_call1.lower_to_chc(
                        ctx,
                        &LocalCtx {
                            error_var: second_error_term.clone(),
                            time_var: lctx.time_var.clone(),
                        },
                    )?
                };

                ctx.type_env.extend(tmp_type_env);

                let spawned_body = func_call_body.concat(func_call1_body);
                if ctx.setting.is_deadlock_mode() {
                    vec![
                        Body {
                            predicates: vec![],
                            constraints: vec![
                                Constraint::Le(first_error_term.clone(), second_error_term.clone()),
                                Constraint::Eq(lctx.error_var.clone(), first_error_term.clone()),
                            ],
                        }
                        .concat(spawned_body.clone()),
                        Body {
                            predicates: vec![],
                            constraints: vec![
                                Constraint::Le(second_error_term.clone(), first_error_term.clone()),
                                Constraint::Eq(lctx.error_var.clone(), second_error_term),
                            ],
                        }
                        .concat(spawned_body),
                    ]
                } else {
                    vec![
                        Body {
                            predicates: vec![],
                            constraints: vec![Constraint::Eq(
                                lctx.error_var.clone(),
                                Term::LOr(Box::new(first_error_term), Box::new(second_error_term)),
                            )],
                        }
                        .concat(spawned_body),
                    ]
                }
            }
            ast::Statement::New {
                payload,
                sender,
                receiver,
                body,
            } => {
                let sender_ty = ast::Type::sender(payload.clone());
                let receiver_ty = ast::Type::receiver(payload.clone());
                ctx.insert_to_type_env(sender, sender_ty.clone())?;
                ctx.insert_to_type_env(receiver, receiver_ty.clone())?;
                let payload_chc_ty = payload.lower_to_chc(&ctx.setting)?;
                let sender_var =
                    ctx.insert_declared_var(sender, sender_ty.lower_to_chc(&ctx.setting)?)?;
                let receiver_var =
                    ctx.insert_declared_var(receiver, receiver_ty.lower_to_chc(&ctx.setting)?)?;
                let (sorted_predicate, _) = ctx.primitive_predicates_for_payload(payload_chc_ty);
                let body = body.lower_to_chc(ctx, lctx)?;
                vec![body.concat(Body {
                    predicates: if ctx.setting.no_timestamps {
                        vec![]
                    } else {
                        vec![PredicateAtom {
                            name: sorted_predicate,
                            args: vec![sender_var.clone()],
                        }]
                    },
                    constraints: vec![Constraint::Eq(receiver_var, sender_var)],
                })]
            }
            ast::Statement::Send {
                sender,
                value,
                body,
            } => {
                let time_var = lctx.time_var.clone();
                let sender_ty = ctx.get_ast_type(sender)?.clone();
                let sender_chc_ty = sender_ty.lower_to_chc(&ctx.setting)?;
                let sender_var = ctx.insert_declared_var(sender, sender_chc_ty.clone())?;
                let new_time_var = ctx.gen_new_var(DEFAULT_TIME_VAR);
                let new_time_term = ctx.insert_declared_var(&new_time_var, Type::Int)?;
                let value_term = value.lower_to_chc(ctx)?;
                let new_lctx = LocalCtx {
                    error_var: lctx.error_var.clone(),
                    time_var: new_time_term.clone(),
                };
                let mut body = body.lower_to_chc(ctx, &new_lctx)?;
                let new_sender = ctx.gen_new_var(sender);
                let new_sender_var = ctx.insert_declared_var(&new_sender, sender_chc_ty)?;
                body.substitute(&HashMap::from([(sender.clone(), new_sender)]));
                vec![body.concat(Body {
                    predicates: vec![],
                    constraints: vec![
                        Constraint::Eq(
                            sender_var,
                            Term::Cons(
                                if ctx.setting.no_timestamps {
                                    value_term.into()
                                } else {
                                    Term::Pair(new_time_term.clone().into(), value_term.into())
                                        .into()
                                },
                                new_sender_var.into(),
                            ),
                        ),
                        Constraint::Le(time_var, new_time_term),
                    ],
                })]
            }
            ast::Statement::Recv {
                receiver,
                var,
                body,
            } => {
                let type_env_before_recv = ctx.type_env.clone();
                let new_time_var = ctx.gen_new_var(DEFAULT_TIME_VAR);
                let new_time_term = ctx.insert_declared_var(&new_time_var, Type::Int)?;
                let tmp_time_var = ctx.gen_new_var(DEFAULT_TIME_VAR);
                let tmp_time_term = ctx.insert_declared_var(&tmp_time_var, Type::Int)?;
                let receiver_ty = ctx.get_ast_type(receiver)?.clone();
                let payload_ty = receiver_ty
                    .payload()
                    .cloned()
                    .ok_or_else(|| anyhow::anyhow!("Variable {} is not a receiver", receiver))?;
                ctx.type_env.insert(var.clone(), payload_ty.clone());
                let mut body = body.lower_to_chc(
                    ctx,
                    &LocalCtx {
                        error_var: lctx.error_var.clone(),
                        time_var: new_time_term.clone(),
                    },
                )?;
                let receiver_chc_ty = receiver_ty.lower_to_chc(&ctx.setting)?;
                let var_term =
                    ctx.insert_declared_var(var, payload_ty.lower_to_chc(&ctx.setting)?)?;
                let receiver_term = ctx.insert_declared_var(receiver, receiver_chc_ty.clone())?;
                let new_receiver = ctx.gen_new_var(receiver);
                let new_receiver_term =
                    ctx.insert_declared_var(&new_receiver, receiver_chc_ty.clone())?;
                body.substitute(&HashMap::from([(receiver.clone(), new_receiver)]));

                let time_constraints = if ctx.setting.no_timestamps {
                    vec![]
                } else {
                    vec![
                        Constraint::Lt(tmp_time_term.clone(), new_time_term.clone()),
                        Constraint::Le(lctx.time_var.clone(), new_time_term.clone()),
                    ]
                };

                let normal_body = Body {
                    predicates: vec![],
                    constraints: vec![Constraint::Eq(
                        receiver_term.clone(),
                        Term::Cons(
                            if ctx.setting.no_timestamps {
                                var_term.into()
                            } else {
                                Term::Pair(tmp_time_term.clone().into(), var_term.into()).into()
                            },
                            new_receiver_term.clone().into(),
                        ),
                    )],
                }
                .concat(Body {
                    predicates: vec![],
                    constraints: time_constraints,
                })
                .concat(body);

                if ctx.setting.is_deadlock_mode() {
                    let type_env_after_recv =
                        std::mem::replace(&mut ctx.type_env, type_env_before_recv);
                    let mut blocked_body = ctx.terminal_closed_body()?;
                    ctx.type_env = type_env_after_recv;
                    blocked_body.constraints.extend([
                        Constraint::Eq(receiver_term, Term::Nil(receiver_chc_ty)),
                        Constraint::Eq(lctx.error_var.clone(), ctx.setting.blocked_status()),
                    ]);
                    vec![normal_body, blocked_body]
                } else {
                    vec![normal_body]
                }
            }
            ast::Statement::Match { scrutinee, arms } => {
                let scrutinee_ty = ctx.get_ast_type(scrutinee)?.clone();
                let ast::Type::Adt(type_name) = &scrutinee_ty else {
                    anyhow::bail!("Variable {} is not an ADT", scrutinee);
                };
                let adt = ctx
                    .adts
                    .get(type_name)
                    .ok_or_else(|| anyhow::anyhow!("unknown ADT type {}", type_name))?
                    .clone();
                let scrutinee_chc_ty = scrutinee_ty.lower_to_chc(&ctx.setting)?;
                let scrutinee_term =
                    ctx.insert_declared_var(scrutinee, scrutinee_chc_ty.clone())?;
                let base_type_env = ctx.type_env.clone();
                let mut bodies = vec![];

                for arm in arms {
                    if &arm.type_name != type_name {
                        anyhow::bail!(
                            "match arm uses ADT {}, expected {}",
                            arm.type_name,
                            type_name
                        );
                    }
                    let variant = adt
                        .variants
                        .iter()
                        .find(|variant| variant.name == arm.variant)
                        .ok_or_else(|| {
                            anyhow::anyhow!("unknown variant {}::{}", type_name, arm.variant)
                        })?;
                    if variant.fields.len() != arm.vars.len() {
                        anyhow::bail!(
                            "variant {}::{} expects {} fields, got {}",
                            type_name,
                            arm.variant,
                            variant.fields.len(),
                            arm.vars.len()
                        );
                    }

                    ctx.type_env = base_type_env.clone();
                    ctx.type_env.remove(scrutinee);
                    let arm_var_map = arm
                        .vars
                        .iter()
                        .map(|var| (var.clone(), ctx.gen_new_var(var)))
                        .collect::<HashMap<_, _>>();
                    for (var, field_ty) in arm.vars.iter().zip(&variant.fields) {
                        let fresh_var = arm_var_map
                            .get(var)
                            .expect("fresh variable should exist for arm binding");
                        ctx.insert_to_type_env(fresh_var, field_ty.clone())?;
                    }
                    let mut arm_body = arm.body.clone();
                    arm_body.substitute_var(&arm_var_map);
                    let body = arm_body.lower_to_chc(ctx, lctx)?;
                    let field_terms = arm
                        .vars
                        .iter()
                        .zip(&variant.fields)
                        .map(|(var, field_ty)| {
                            let fresh_var = arm_var_map
                                .get(var)
                                .expect("fresh variable should exist for arm binding");
                            ctx.insert_declared_var(fresh_var, field_ty.lower_to_chc(&ctx.setting)?)
                        })
                        .collect::<Result<Vec<_>>>()?;
                    bodies.push(
                        Body {
                            predicates: vec![],
                            constraints: vec![Constraint::Eq(
                                scrutinee_term.clone(),
                                Term::Ctor {
                                    name: adt_constructor_name(type_name, &arm.variant),
                                    args: field_terms.clone(),
                                },
                            )],
                        }
                        .concat(body),
                    );
                }

                ctx.type_env = base_type_env;
                bodies
            }
            ast::Statement::Dup { sender, var, body } => {
                let sender_ty = ctx.get_ast_type(sender)?.clone();
                let payload_ty = sender_ty
                    .payload()
                    .cloned()
                    .ok_or_else(|| anyhow::anyhow!("Variable {} is not a sender", sender))?;
                let (_, merge_predicate) =
                    ctx.primitive_predicates_for_payload(payload_ty.lower_to_chc(&ctx.setting)?);
                let sender_chc_ty = sender_ty.lower_to_chc(&ctx.setting)?;
                let sender_term = ctx.insert_declared_var(sender, sender_chc_ty.clone())?;
                let new_sender_var = ctx.gen_new_var(sender);
                let new_sender_term =
                    ctx.insert_declared_var(&new_sender_var, sender_chc_ty.clone())?;
                let var_term = ctx.insert_declared_var(var, sender_chc_ty)?;
                ctx.type_env.insert(var.clone(), sender_ty);
                let mut body = body.lower_to_chc(ctx, lctx)?;
                body.substitute(&HashMap::from([(sender.clone(), new_sender_var)]));
                vec![
                    Body {
                        predicates: vec![PredicateAtom {
                            name: merge_predicate,
                            args: vec![var_term, new_sender_term, sender_term],
                        }],
                        constraints: vec![],
                    }
                    .concat(body),
                ]
            }
        })
    }
}

impl ast::Function {
    fn lower_to_chc(&self, ctx: &mut Ctx) -> Result<Vec<Clause>> {
        let mut clauses = vec![];
        let error_var = ctx.insert_declared_var(DEFAULT_ERROR_VAR, ctx.setting.status_type())?;
        let time_var = ctx.insert_declared_var(DEFAULT_TIME_VAR, Type::Int)?;

        for (param_name, param_type) in &self.params {
            let chc_type = param_type.lower_to_chc(&ctx.setting)?;
            ctx.insert_to_type_env(param_name, param_type.clone())?;
            ctx.insert_declared_var(param_name.clone(), chc_type)?;
        }

        let param_terms: Vec<Term> = self
            .params
            .iter()
            .map(|(param_name, _)| Term::Var(param_name.clone()))
            .collect::<Vec<Term>>();

        if !ctx.setting.is_deadlock_mode() {
            clauses.push(Clause {
                forall: ctx.var_declarations.clone().into_iter().collect(),
                head: Some(PredicateAtom {
                    name: self.name.clone(),
                    args: [
                        if ctx.setting.no_timestamps {
                            vec![ctx.setting.terminated_status()]
                        } else {
                            vec![ctx.setting.terminated_status(), time_var.clone()]
                        },
                        param_terms.clone(),
                    ]
                    .concat(),
                }),
                body: ctx.terminal_closed_body()?,
            });
        }

        let lctx = LocalCtx {
            error_var: error_var.clone(),
            time_var: time_var.clone(),
        };

        let disj_body = self.body.lower_to_chc(ctx, &lctx)?;

        for body in disj_body {
            clauses.push(Clause {
                forall: ctx.var_declarations.clone().into_iter().collect(),
                head: Some(PredicateAtom {
                    name: self.name.clone(),
                    args: [
                        if ctx.setting.no_timestamps {
                            vec![error_var.clone()]
                        } else {
                            vec![error_var.clone(), time_var.clone()]
                        },
                        param_terms.clone(),
                    ]
                    .concat(),
                }),
                body,
            });
        }

        Ok(clauses)
    }
}

impl ast::Program {
    pub fn lower_to_chc(&self, setting: Setting) -> Result<CHC> {
        let mut chc = CHC::init_premitive(&setting);
        chc.datatypes = self
            .adts
            .iter()
            .map(|adt| lower_datatype_def(adt, &setting))
            .collect::<Result<Vec<_>>>()?;
        let mut ctx = Ctx {
            fun_declarations: chc.fun_declarations.clone(),
            adts: self
                .adts
                .iter()
                .map(|adt| (adt.name.clone(), adt.clone()))
                .collect(),
            setting,
            ..Default::default()
        };
        let func_type_env: HashMap<ast::VarName, ast::Type> = self
            .functions
            .values()
            .map(|func| {
                (
                    func.name.clone(),
                    ast::Type::Func {
                        params: func.params.iter().map(|(_, ty)| ty.clone()).collect(),
                    },
                )
            })
            .collect();

        for func in self.functions.values() {
            ctx.type_env = func_type_env.clone();
            ctx.var_declarations.clear();
            let predicate_args = {
                let mut params = if ctx.setting.no_timestamps {
                    vec![ctx.setting.status_type()]
                } else {
                    vec![ctx.setting.status_type(), Type::Int]
                };
                params.extend(
                    func.params
                        .iter()
                        .map(|(_, ty)| ty.lower_to_chc(&ctx.setting))
                        .collect::<Result<Vec<_>>>()?,
                );
                params
            };
            ctx.fun_declarations
                .insert(func.name.clone(), predicate_args);
            let mut func_clauses = func.lower_to_chc(&mut ctx)?;
            chc.clauses.append(&mut func_clauses);
        }

        // init function call
        ctx.type_env = func_type_env;
        ctx.var_declarations.clear();

        let init_free_vars = self.init.free_vars();

        for free_var in init_free_vars {
            ctx.type_env.insert(free_var.clone(), ast::Type::Int);
            ctx.var_declarations.insert(free_var, Type::Int);
        }

        let time_var = ctx.insert_declared_var(DEFAULT_TIME_VAR, Type::Int)?;
        let init_query_status = ctx.setting.init_query_status();

        let init_body = self.init.lower_to_chc(
            &mut ctx,
            &LocalCtx {
                error_var: init_query_status,
                time_var: time_var.clone(),
            },
        )?;

        chc.clauses.push(Clause {
            forall: ctx.var_declarations.clone().into_iter().collect(),
            head: None,
            body: init_body,
        });

        for payload_ty in ctx.primitive_payload_types.clone() {
            chc.clauses
                .extend(CHC::primitive_clauses(&ctx.setting, payload_ty));
        }

        for payload in ctx.closed_payload_types.clone() {
            chc.clauses
                .extend(ctx.closed_clauses_for_payload(&payload)?);
        }

        for ty in ctx.closed_value_types.clone() {
            chc.clauses.extend(ctx.closed_clauses_for_adt_value(&ty)?);
        }

        Ok(CHC {
            clauses: chc.clauses,
            fun_declarations: ctx.fun_declarations,
            datatypes: chc.datatypes,
            setting: ctx.setting,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{chc::CheckMode, core::parser};

    fn deadlock_setting(no_timestamps: bool) -> Setting {
        Setting {
            no_timestamps,
            check_mode: CheckMode::DeadlockFreedom,
        }
    }

    #[test]
    fn monomorphizes_primitives_for_channel_payloads() {
        let program = parser::parse_program(
            r#"
            init = main()

            main() = new<Sender<int>> s, r in proc(s, r)
            proc(s: Sender<Sender<int>>, r: Receiver<Sender<int>>) = let s2 = dup s in fail_with(s, s2, r)
            fail_with(s1: Sender<Sender<int>>, s2: Sender<Sender<int>>, r: Receiver<Sender<int>>) = fail
            "#,
        )
        .expect("program should parse");

        let chc = program
            .lower_to_chc(Setting {
                no_timestamps: false,
                ..Setting::default()
            })
            .expect("program should lower");

        assert!(
            chc.fun_declarations
                .contains_key("%Sorted$Lst_Pair_Int_Int")
        );
        assert!(chc.fun_declarations.contains_key("%Merge$Lst_Pair_Int_Int"));
        assert!(chc.fun_declarations.contains_key("%Closed$Sender_Int"));
    }

    #[test]
    fn closed_receiver_payload_requires_nested_sender_to_be_empty() {
        let program = parser::parse_program(
            r#"
            init = main()

            main() = new<Sender<int>> s, r in fail_with_receiver(s, r)
            fail_with_receiver(s: Sender<Sender<int>>, r: Receiver<Sender<int>>) = fail
            "#,
        )
        .expect("program should parse");

        let chc = program
            .lower_to_chc(Setting {
                no_timestamps: false,
                ..Setting::default()
            })
            .expect("program should lower");
        let recursive_closed_clause = chc
            .clauses
            .iter()
            .find(|clause| {
                clause
                    .head
                    .as_ref()
                    .is_some_and(|head| head.name == "%Closed$Sender_Int")
                    && !clause.forall.is_empty()
            })
            .expect("recursive closed clause should exist");

        assert!(
            recursive_closed_clause
                .body
                .constraints
                .iter()
                .any(|constraint| {
                    matches!(
                        constraint,
                        Constraint::Eq(Term::Val(term), Term::Nil(_))
                            if **term == Term::Var("p".to_string())
                    )
                })
        );
    }

    #[test]
    fn lowers_linear_adt_and_closed_value_predicate() {
        let program = parser::parse_program(
            r#"
            data Box = Hold(Sender<int>)

            init = main()

            main() = new s, r in fail_with(Box::Hold(s), r)
            fail_with(b: Box, r: Receiver<int>) = fail
            "#,
        )
        .expect("program should parse");

        let chc = program
            .lower_to_chc(Setting {
                no_timestamps: false,
                ..Setting::default()
            })
            .expect("program should lower");
        let output = chc.to_string();

        assert!(output.contains("(declare-datatypes ((Adt$Box 0))"));
        assert!(output.contains("Adt$Box$Hold"));
        assert!(chc.fun_declarations.contains_key("%ClosedValue$Adt_Box"));
        assert!(
            output.contains("(= %field0 (as nil (Lst (Pair Int Int))))"),
            "{output}"
        );
    }

    #[test]
    fn freshens_match_arm_bindings_with_the_same_name() {
        let program = parser::parse_program(
            r#"
            data T = A(int) | B(Sender<int>)

            init = main()

            main() = new s, r in use(T::B(s), r)
            use(t: T, r: Receiver<int>) = match t {
                T::A(x) => done(r),
                T::B(x) => done_with_sender(x, r),
            }
            done(r: Receiver<int>) = ()
            done_with_sender(x: Sender<int>, r: Receiver<int>) = ()
            "#,
        )
        .expect("program should parse");

        program
            .lower_to_chc(Setting {
                no_timestamps: false,
                ..Setting::default()
            })
            .expect("program should lower without arm binding conflicts");
    }

    #[test]
    fn deadlock_mode_uses_int_status_without_status_datatypes() {
        let program = parser::parse_program(
            r#"
            init = main()

            main() = ()
            "#,
        )
        .expect("program should parse");

        let chc = program
            .lower_to_chc(deadlock_setting(false))
            .expect("program should lower");

        assert_eq!(chc.fun_declarations["main"][0], Type::Int);
        let output = chc.to_string();
        assert!(!output.contains("Status"), "{output}");
        assert!(!output.contains("Join"), "{output}");
    }

    #[test]
    fn deadlock_recv_emits_normal_and_blocked_clauses() {
        let program = parser::parse_program(
            r#"
            init = main()

            main() = new s, r in read(s, r)
            read(s: Sender, r: Receiver) = let v = recv r in done(s, r)
            done(s: Sender, r: Receiver) = ()
            "#,
        )
        .expect("program should parse");

        let chc = program
            .lower_to_chc(deadlock_setting(false))
            .expect("program should lower");
        let read_clauses = chc
            .clauses
            .iter()
            .filter(|clause| clause.head.as_ref().is_some_and(|head| head.name == "read"))
            .collect::<Vec<_>>();

        assert!(read_clauses.iter().any(|clause| {
            clause.body.constraints.iter().any(|constraint| {
                matches!(
                    constraint,
                    Constraint::Eq(Term::Var(receiver), Term::Cons(_, _))
                        if receiver == "r"
                )
            })
        }));
        assert!(read_clauses.iter().any(|clause| {
            let has_blocked_status = clause.body.constraints.iter().any(|constraint| {
                matches!(
                    constraint,
                    Constraint::Eq(Term::Var(status), Term::Int(0))
                        if status == DEFAULT_ERROR_VAR
                )
            });
            let has_nil_receiver = clause.body.constraints.iter().any(|constraint| {
                matches!(
                    constraint,
                    Constraint::Eq(Term::Var(receiver), Term::Nil(_))
                        if receiver == "r"
                )
            });
            let closes_sender = clause.body.constraints.iter().any(|constraint| {
                matches!(
                    constraint,
                    Constraint::Eq(Term::Var(sender), Term::Nil(_))
                        if sender == "s"
                )
            });

            has_blocked_status && has_nil_receiver && closes_sender
        }));
    }

    #[test]
    fn deadlock_mode_does_not_add_synthetic_termination_for_non_unit_functions() {
        let program = parser::parse_program(
            r#"
            init = main()

            main() = new s, r in wait(s, r)
            wait(s: Sender, r: Receiver) = let v = recv r in done(s, r)
            done(s: Sender, r: Receiver) = ()
            "#,
        )
        .expect("program should parse");

        let chc = program
            .lower_to_chc(deadlock_setting(false))
            .expect("program should lower");

        assert!(!chc.clauses.iter().any(|clause| {
            clause.head.as_ref().is_some_and(|head| {
                head.name == "wait" && matches!(head.args.first(), Some(Term::Int(1)))
            })
        }));
        assert!(chc.clauses.iter().any(|clause| {
            clause.head.as_ref().is_some_and(|head| head.name == "done")
                && clause.body.constraints.iter().any(|constraint| {
                    matches!(
                        constraint,
                        Constraint::Eq(Term::Var(status), Term::Int(1))
                            if status == DEFAULT_ERROR_VAR
                    )
                })
        }));
    }

    #[test]
    fn deadlock_spawn_lowers_status_join_to_min_clauses() {
        let program = parser::parse_program(
            r#"
            init = main()

            main() = spawn(left()); right()
            left() = ()
            right() = ()
            "#,
        )
        .expect("program should parse");

        let chc = program
            .lower_to_chc(deadlock_setting(false))
            .expect("program should lower");
        let spawn_clauses = chc
            .clauses
            .iter()
            .filter(|clause| {
                clause.head.as_ref().is_some_and(|head| head.name == "main")
                    && clause
                        .body
                        .constraints
                        .iter()
                        .any(|constraint| matches!(constraint, Constraint::Le(_, _)))
            })
            .collect::<Vec<_>>();

        assert_eq!(spawn_clauses.len(), 2);
        assert!(spawn_clauses.iter().any(|clause| {
            clause.body.constraints.iter().any(|constraint| {
                matches!(
                    constraint,
                    Constraint::Le(Term::Var(first), Term::Var(second))
                        if first == "%b%0" && second == "%b%1"
                )
            }) && clause.body.constraints.iter().any(|constraint| {
                matches!(
                    constraint,
                    Constraint::Eq(Term::Var(status), Term::Var(first))
                        if status == DEFAULT_ERROR_VAR && first == "%b%0"
                )
            })
        }));
        assert!(spawn_clauses.iter().any(|clause| {
            clause.body.constraints.iter().any(|constraint| {
                matches!(
                    constraint,
                    Constraint::Le(Term::Var(second), Term::Var(first))
                        if second == "%b%1" && first == "%b%0"
                )
            }) && clause.body.constraints.iter().any(|constraint| {
                matches!(
                    constraint,
                    Constraint::Eq(Term::Var(status), Term::Var(second))
                        if status == DEFAULT_ERROR_VAR && second == "%b%1"
                )
            })
        }));
    }

    #[test]
    fn deadlock_no_timestamps_recv_still_emits_blocked_clause() {
        let program = parser::parse_program(
            r#"
            init = main()

            main() = new s, r in read(s, r)
            read(s: Sender, r: Receiver) = let v = recv r in done(s, r)
            done(s: Sender, r: Receiver) = ()
            "#,
        )
        .expect("program should parse");

        let chc = program
            .lower_to_chc(deadlock_setting(true))
            .expect("program should lower");

        assert!(chc.clauses.iter().any(|clause| {
            clause.head.as_ref().is_some_and(|head| head.name == "read")
                && clause.body.constraints.iter().any(|constraint| {
                    matches!(
                        constraint,
                        Constraint::Eq(
                            Term::Var(receiver),
                            Term::Nil(Type::Lst(inner))
                        ) if receiver == "r" && **inner == Type::Int
                    )
                })
                && clause.body.constraints.iter().any(|constraint| {
                    matches!(
                        constraint,
                        Constraint::Eq(Term::Var(status), Term::Int(0))
                            if status == DEFAULT_ERROR_VAR
                    )
                })
        }));
    }
}

use anyhow::Result;
use std::collections::HashMap;

use crate::{
    chc::{
        Body, CHC, Clause, Constraint, DisjunctiveBody, PredicateAtom, PredicateName, Setting,
        Term, Type,
    },
    core::ast::{self},
};

static CLOSED_PREDICATE: &str = "%Closed";

#[derive(Debug, Default)]
pub struct Ctx {
    var_declarations: HashMap<PredicateName, Type>,
    fun_declarations: HashMap<PredicateName, Vec<Type>>,
    type_env: HashMap<ast::VarName, ast::Type>,
    primitive_payload_types: Vec<Type>,
    closed_payload_types: Vec<ast::Type>,
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
            ast::Type::Int | ast::Type::Func { .. } | ast::Type::Receiver(_) => {}
        }
        Ok(())
    }

    fn terminal_closed_body(&mut self) -> Result<Body> {
        let mut body = Body::default();
        for (var, ty) in self.collect_linear_vars() {
            let term = self.insert_declared_var(var, ty.lower_to_chc(&self.setting)?)?;
            self.add_closed_value_conditions(&mut body, term, &ty)?;
        }
        Ok(body)
    }
}

fn ast_type_suffix(ty: &ast::Type) -> String {
    match ty {
        ast::Type::Int => "Int".to_string(),
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

fn needs_closed_value(ty: &ast::Type) -> bool {
    match ty {
        ast::Type::Sender(_) => true,
        ast::Type::Receiver(payload) => needs_closed_value(payload),
        ast::Type::Int | ast::Type::Func { .. } => false,
    }
}

fn closed_list_type(payload: &ast::Type, setting: &Setting) -> Result<Type> {
    Ok(Type::prophecy(
        setting.no_timestamps,
        payload.lower_to_chc(setting)?,
    ))
}

fn add_closed_value_to_body(
    body: &mut Body,
    term: Term,
    ty: &ast::Type,
    setting: &Setting,
) -> Result<()> {
    match ty {
        ast::Type::Sender(_) => {
            body.constraints
                .push(Constraint::Eq(term, Term::Nil(ty.lower_to_chc(setting)?)));
        }
        ast::Type::Receiver(payload) if needs_closed_value(payload) => {
            body.predicates.push(PredicateAtom {
                name: closed_predicate_name(payload),
                args: vec![term],
            });
        }
        ast::Type::Int | ast::Type::Func { .. } | ast::Type::Receiver(_) => {}
    }
    Ok(())
}

fn closed_clauses_for_payload(setting: &Setting, payload: &ast::Type) -> Result<Vec<Clause>> {
    let predicate_name = closed_predicate_name(payload);
    let list_ty = closed_list_type(payload, setting)?;
    let payload_ty = payload.lower_to_chc(setting)?;
    let item_ty = if setting.no_timestamps {
        payload_ty
    } else {
        Type::timestamped_value(payload_ty)
    };
    let value_term = if setting.no_timestamps {
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
    add_closed_value_to_body(&mut recursive_body, value_term, payload, setting)?;

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

#[derive(Debug)]
pub struct LocalCtx {
    pub error_var: Term,
    pub time_var: Term,
}

impl ast::Type {
    fn lower_to_chc(&self, setting: &Setting) -> Result<Type> {
        Ok(match self {
            ast::Type::Int => Type::Int,
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
                vec![]
            }

            ast::Statement::Fail => {
                let mut body = ctx.terminal_closed_body()?;
                let error_var = lctx.error_var.clone();
                body.constraints.push(Constraint::Eq(
                    error_var,
                    Term::Bool(matches!(self, ast::Statement::Fail)),
                ));
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
                let first_error_term = ctx.insert_declared_var(&first_error_var, Type::Bool)?;
                let second_error_var = ctx.gen_new_var(DEFAULT_ERROR_VAR);
                let second_error_term = ctx.insert_declared_var(&second_error_var, Type::Bool)?;

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

                vec![
                    Body {
                        predicates: vec![],
                        constraints: vec![Constraint::Eq(
                            lctx.error_var.clone(),
                            Term::LOr(Box::new(first_error_term), Box::new(second_error_term)),
                        )],
                    }
                    .concat(func_call_body.concat(func_call1_body)),
                ]
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
                let new_receiver_term = ctx.insert_declared_var(&new_receiver, receiver_chc_ty)?;
                body.substitute(&HashMap::from([(receiver.clone(), new_receiver)]));

                let time_constraints = if ctx.setting.no_timestamps {
                    vec![]
                } else {
                    vec![
                        Constraint::Lt(tmp_time_term.clone(), new_time_term.clone()),
                        Constraint::Le(lctx.time_var.clone(), new_time_term.clone()),
                    ]
                };

                vec![
                    Body {
                        predicates: vec![],
                        constraints: vec![Constraint::Eq(
                            receiver_term,
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
                    .concat(body),
                ]
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
        let error_var = ctx.insert_declared_var(DEFAULT_ERROR_VAR, Type::Bool)?;
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

        clauses.push(Clause {
            forall: ctx.var_declarations.clone().into_iter().collect(),
            head: Some(PredicateAtom {
                name: self.name.clone(),
                args: [
                    if ctx.setting.no_timestamps {
                        vec![Term::Bool(false)]
                    } else {
                        vec![Term::Bool(false), time_var.clone()]
                    },
                    param_terms.clone(),
                ]
                .concat(),
            }),
            body: ctx.terminal_closed_body()?,
        });

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
        let mut ctx = Ctx {
            fun_declarations: chc.fun_declarations.clone(),
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
                    vec![Type::Bool]
                } else {
                    vec![Type::Bool, Type::Int]
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

        let init_body = self.init.lower_to_chc(
            &mut ctx,
            &LocalCtx {
                error_var: Term::Bool(true),
                time_var: time_var.clone(),
            },
        )?;

        chc.clauses.push(Clause {
            forall: ctx.var_declarations.into_iter().collect(),
            head: None,
            body: init_body,
        });

        for payload_ty in ctx.primitive_payload_types.clone() {
            chc.clauses
                .extend(CHC::primitive_clauses(&ctx.setting, payload_ty));
        }

        for payload in ctx.closed_payload_types.clone() {
            chc.clauses
                .extend(closed_clauses_for_payload(&ctx.setting, &payload)?);
        }

        Ok(CHC {
            clauses: chc.clauses,
            fun_declarations: ctx.fun_declarations,
            setting: ctx.setting,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::parser;

    #[test]
    fn monomorphizes_primitives_for_channel_payloads() {
        let program = parser::parse_program(
            r#"
            init = main()

            main() = new<Sender<int>> s, r in proc(s, r)
            proc(s: Sender<Sender<int>>, r: Receiver<Sender<int>>) = let s2 = dup s in fail_with(s2, r)
            fail_with(s: Sender<Sender<int>>, r: Receiver<Sender<int>>) = fail
            "#,
        )
        .expect("program should parse");

        let chc = program
            .lower_to_chc(Setting {
                no_timestamps: false,
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

            main() = new<Sender<int>> s, r in fail_with_receiver(r)
            fail_with_receiver(r: Receiver<Sender<int>>) = fail
            "#,
        )
        .expect("program should parse");

        let chc = program
            .lower_to_chc(Setting {
                no_timestamps: false,
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
}

use anyhow::Result;
use std::collections::HashMap;

use crate::{
    ast::{self},
    chc::{
        Body, Clause, Constraint, DisjunctiveBody, PredicateAtom, PredicateName, Setting, Term,
        Type, CHC, MERGE_PREDICATE, SORTED_PREDICATE,
    },
};

#[derive(Debug, Default)]
pub struct Ctx {
    var_declarations: HashMap<PredicateName, Type>,
    fun_declarations: HashMap<PredicateName, Vec<Type>>,
    type_env: HashMap<ast::VarName, ast::Type>,
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

    fn collect_out_channels(&self) -> Vec<ast::VarName> {
        self.type_env
            .iter()
            .filter_map(|(var, ty)| match ty {
                ast::Type::Sender => Some(var.clone()),
                _ => None,
            })
            .collect()
    }

    fn gen_new_var(&mut self, previous_var: &str) -> ast::VarName {
        let previous_var = previous_var.trim_end_matches('%');
        let var_name = format!("{}%{}", previous_var, self.unused_num);
        self.unused_num += 1;
        var_name
    }
}

#[derive(Debug)]
pub struct LocalCtx {
    pub error_var: Term,
    pub time_var: Term,
}

impl ast::Type {
    fn lower_to_chc(&self) -> Result<Type> {
        Ok(match self {
            ast::Type::Int => Type::Int,
            ast::Type::Sender | ast::Type::Receiver => Type::Prophecy,
            ast::Type::Func { params } => {
                let chc_params = params
                    .iter()
                    .map(|p| p.lower_to_chc())
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
                let chc_ty = ast_ty.lower_to_chc()?;
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
            ast::Statement::Fail | ast::Statement::Unit => {
                let mut constraints = vec![];
                let error_var = lctx.error_var.clone();
                constraints.push(Constraint::Eq(
                    error_var,
                    Term::Bool(matches!(self, ast::Statement::Fail)),
                ));
                let out_channels = ctx.collect_out_channels();
                for chan in out_channels {
                    let chan_var = ctx.insert_declared_var(chan, Type::Prophecy)?;
                    constraints.push(Constraint::Eq(chan_var, Term::Nil));
                }
                vec![Body {
                    predicates: vec![],
                    constraints,
                }]
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

                vec![Body {
                    predicates: vec![],
                    constraints: vec![Constraint::Eq(
                        lctx.error_var.clone(),
                        Term::LOr(Box::new(first_error_term), Box::new(second_error_term)),
                    )],
                }
                .concat(func_call_body.concat(func_call1_body))]
            }
            ast::Statement::New {
                sender,
                receiver,
                body,
            } => {
                ctx.insert_to_type_env(sender, ast::Type::Sender)?;
                ctx.insert_to_type_env(receiver, ast::Type::Receiver)?;
                let sender_var = ctx.insert_declared_var(sender, Type::Prophecy)?;
                let receiver_var = ctx.insert_declared_var(receiver, Type::Prophecy)?;
                let body = body.lower_to_chc(ctx, lctx)?;
                vec![body.concat(Body {
                    predicates: if ctx.setting.no_timestamps {
                        vec![]
                    } else {
                        vec![PredicateAtom {
                            name: SORTED_PREDICATE.to_string(),
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
                let sender_var = ctx.insert_declared_var(sender, Type::Prophecy)?;
                let new_time_var = ctx.gen_new_var(DEFAULT_TIME_VAR);
                let new_time_term = ctx.insert_declared_var(&new_time_var, Type::Int)?;
                let value_term = value.lower_to_chc(ctx)?;
                let new_lctx = LocalCtx {
                    error_var: lctx.error_var.clone(),
                    time_var: new_time_term.clone(),
                };
                let mut body = body.lower_to_chc(ctx, &new_lctx)?;
                let new_sender = ctx.gen_new_var(sender);
                let new_sender_var = ctx.insert_declared_var(&new_sender, Type::Prophecy)?;
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
                ctx.type_env.insert(var.clone(), ast::Type::Int);
                let mut body = body.lower_to_chc(
                    ctx,
                    &LocalCtx {
                        error_var: lctx.error_var.clone(),
                        time_var: new_time_term.clone(),
                    },
                )?;
                let var_term = ctx.insert_declared_var(var, Type::Int)?;
                let receiver_term = ctx.insert_declared_var(receiver, Type::Prophecy)?;
                let new_receiver = ctx.gen_new_var(receiver);
                let new_receiver_term = ctx.insert_declared_var(&new_receiver, Type::Prophecy)?;
                body.substitute(&HashMap::from([(receiver.clone(), new_receiver)]));

                let time_constraints = if ctx.setting.no_timestamps {
                    vec![]
                } else {
                    vec![
                        Constraint::Lt(tmp_time_term.clone(), new_time_term.clone()),
                        Constraint::Le(lctx.time_var.clone(), new_time_term.clone()),
                    ]
                };

                let out_channels = ctx.collect_out_channels();
                let out_channels_constraints = out_channels
                    .into_iter()
                    .map(|chan| {
                        let chan_var = ctx.insert_declared_var(chan, Type::Prophecy)?;
                        Ok(Constraint::Eq(chan_var, Term::Nil))
                    })
                    .collect::<Result<Vec<_>>>()?;

                vec![
                    Body {
                        predicates: vec![],
                        constraints: [
                            vec![
                                Constraint::Eq(receiver_term.clone(), Term::Nil),
                                Constraint::Eq(lctx.error_var.clone(), Term::Bool(false)),
                            ],
                            out_channels_constraints,
                        ]
                        .concat(),
                    },
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
                let sender_term = ctx.insert_declared_var(sender, Type::Prophecy)?;
                let new_sender_var = ctx.gen_new_var(sender);
                let new_sender_term = ctx.insert_declared_var(&new_sender_var, Type::Prophecy)?;
                let var_term = ctx.insert_declared_var(var, Type::Prophecy)?;
                ctx.type_env.insert(var.clone(), ast::Type::Sender);
                let mut body = body.lower_to_chc(ctx, lctx)?;
                body.substitute(&HashMap::from([(sender.clone(), new_sender_var)]));
                vec![Body {
                    predicates: vec![PredicateAtom {
                        name: MERGE_PREDICATE.to_string(),
                        args: vec![var_term, new_sender_term, sender_term],
                    }],
                    constraints: vec![],
                }
                .concat(body)]
            }
        })
    }
}

impl ast::Function {
    fn lower_to_chc(&self, ctx: &mut Ctx) -> Result<Vec<Clause>> {
        let mut clauses = vec![];
        let error_var = ctx.insert_declared_var(DEFAULT_ERROR_VAR, Type::Bool)?;
        let time_var = ctx.insert_declared_var(DEFAULT_TIME_VAR, Type::Int)?;

        let mut out_channels = vec![];

        for (param_name, param_type) in &self.params {
            let chc_type = param_type.lower_to_chc()?;
            ctx.insert_to_type_env(param_name, param_type.clone())?;
            ctx.insert_declared_var(param_name.clone(), chc_type)?;
            if param_type == &ast::Type::Sender {
                out_channels.push(param_name.clone());
            }
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
            body: {
                let mut constraints = vec![];
                for chan in out_channels {
                    constraints.push(Constraint::Eq(Term::Var(chan), Term::Nil));
                }
                Body {
                    predicates: vec![],
                    constraints,
                }
            },
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
                        .map(|(_, ty)| ty.lower_to_chc())
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

        Ok(CHC {
            clauses: chc.clauses,
            fun_declarations: ctx.fun_declarations,
            setting: ctx.setting,
        })
    }
}

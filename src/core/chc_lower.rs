use anyhow::Result;
use std::{collections::HashMap, marker::PhantomData};

use crate::{
    chc::{
        Body, CHC, CheckMode, Clause, Constraint, Datatype, DatatypeVariant, DisjunctiveBody,
        PredicateAtom, PredicateName, Setting, Term, Type, status_blocked, status_fail,
        status_terminated,
    },
    core::ast::{self},
};

static CLOSED_PREDICATE: &str = "%Closed";

trait TimeEncoding {
    fn channel_item_type(payload_ty: Type) -> Type;
    fn predicate_arg_types(status_ty: Type) -> Vec<Type>;
    fn channel_item_value(item: Term) -> Term;
    fn predicate_args(status: Term, time: Term) -> Vec<Term>;
    fn sorted_new_predicates(sorted_predicate: PredicateName, sender: Term) -> Vec<PredicateAtom>;
    fn sorted_primitive_clauses(sorted_predicate: PredicateName, prophecy_ty: Type) -> Vec<Clause>;
    fn initial_time_var<P: LoweringPolicy>(ctx: &mut Ctx<P>) -> Result<Term>;
    fn send_item_and_lctx<P: LoweringPolicy>(
        ctx: &mut Ctx<P>,
        lctx: &LocalCtx,
        value: Term,
    ) -> Result<(Term, LocalCtx, Vec<Constraint>)>;
    fn recv_lctx<P: LoweringPolicy>(ctx: &mut Ctx<P>, lctx: &LocalCtx) -> Result<LocalCtx>;
    fn recv_item_and_constraints<P: LoweringPolicy>(
        ctx: &mut Ctx<P>,
        lctx: &LocalCtx,
        recv_lctx: &LocalCtx,
        value: Term,
    ) -> Result<(Term, Vec<Constraint>)>;
}

trait CheckEncoding {
    fn status_type() -> Type;
    fn status(status: CheckStatus) -> Term;
    fn unit_body<P: LoweringPolicy>(ctx: &mut Ctx<P>, lctx: &LocalCtx) -> Result<Option<Body>>;
    fn spawn_status_bodies(
        parent_error: Term,
        first_error: Term,
        second_error: Term,
    ) -> DisjunctiveBody;
    fn recv_blocked_body<P: LoweringPolicy>(
        ctx: &mut Ctx<P>,
        lctx: &LocalCtx,
        receiver_term: Term,
        receiver_ty: Type,
        type_env_before_recv: HashMap<ast::VarName, ast::Type>,
    ) -> Result<Option<Body>>;
    fn synthetic_termination_clause<P: LoweringPolicy>(
        ctx: &mut Ctx<P>,
        name: &str,
        time_var: Term,
        param_terms: &[Term],
    ) -> Result<Option<Clause>>;
}

#[derive(Clone, Copy)]
enum CheckStatus {
    Failure,
    Terminated,
    InitQuery,
    Blocked,
}

trait LoweringPolicy {
    type Time: TimeEncoding;
    type Check: CheckEncoding;
}

struct Timestamped;
struct Untimestamped;
struct FailReachabilityCheck;
struct DeadlockFreedomCheck;

struct Policy<T, C>(PhantomData<(T, C)>);

impl<T: TimeEncoding, C: CheckEncoding> LoweringPolicy for Policy<T, C> {
    type Time = T;
    type Check = C;
}

impl TimeEncoding for Timestamped {
    fn channel_item_type(payload_ty: Type) -> Type {
        Type::timestamped_value(payload_ty)
    }

    fn predicate_arg_types(status_ty: Type) -> Vec<Type> {
        vec![status_ty, Type::Int]
    }

    fn channel_item_value(item: Term) -> Term {
        Term::Val(item.into())
    }

    fn predicate_args(status: Term, time: Term) -> Vec<Term> {
        vec![status, time]
    }

    fn sorted_new_predicates(sorted_predicate: PredicateName, sender: Term) -> Vec<PredicateAtom> {
        vec![PredicateAtom {
            name: sorted_predicate,
            args: vec![sender],
        }]
    }

    fn sorted_primitive_clauses(sorted_predicate: PredicateName, prophecy_ty: Type) -> Vec<Clause> {
        let timestamped_value_ty = match &prophecy_ty {
            Type::Lst(inner) => (**inner).clone(),
            _ => unreachable!("prophecy type is always a list"),
        };
        vec![
            Clause {
                forall: vec![],
                head: Some(PredicateAtom {
                    name: sorted_predicate.clone(),
                    args: vec![Term::Nil(prophecy_ty.clone())],
                }),
                body: Body::default(),
            },
            Clause {
                forall: vec![
                    ("l".to_string(), prophecy_ty.clone()),
                    ("p".to_string(), timestamped_value_ty.clone()),
                ],
                head: Some(PredicateAtom {
                    name: sorted_predicate.clone(),
                    args: vec![Term::Var("l".to_string())],
                }),
                body: Body {
                    predicates: vec![],
                    constraints: vec![Constraint::Eq(
                        Term::Var("l".to_string()),
                        Term::Cons(
                            Term::Var("p".to_string()).into(),
                            Term::Nil(prophecy_ty.clone()).into(),
                        ),
                    )],
                },
            },
            Clause {
                forall: vec![
                    ("l".to_string(), prophecy_ty.clone()),
                    ("l2".to_string(), prophecy_ty.clone()),
                    ("l3".to_string(), prophecy_ty.clone()),
                    ("p".to_string(), timestamped_value_ty.clone()),
                    ("p2".to_string(), timestamped_value_ty),
                ],
                head: Some(PredicateAtom {
                    name: sorted_predicate.clone(),
                    args: vec![Term::Var("l".to_string())],
                }),
                body: Body {
                    predicates: vec![PredicateAtom {
                        name: sorted_predicate,
                        args: vec![Term::Var("l2".to_string())],
                    }],
                    constraints: vec![
                        Constraint::Eq(
                            Term::Var("l".to_string()),
                            Term::Cons(
                                Term::Var("p".to_string()).into(),
                                Term::Var("l2".to_string()).into(),
                            ),
                        ),
                        Constraint::Eq(
                            Term::Var("l2".to_string()),
                            Term::Cons(
                                Term::Var("p2".to_string()).into(),
                                Term::Var("l3".to_string()).into(),
                            ),
                        ),
                        Constraint::Le(
                            Term::Key(Term::Var("p".to_string()).into()),
                            Term::Key(Term::Var("p2".to_string()).into()),
                        ),
                    ],
                },
            },
        ]
    }

    fn initial_time_var<P: LoweringPolicy>(ctx: &mut Ctx<P>) -> Result<Term> {
        ctx.insert_declared_var(DEFAULT_TIME_VAR, Type::Int)
    }

    fn send_item_and_lctx<P: LoweringPolicy>(
        ctx: &mut Ctx<P>,
        lctx: &LocalCtx,
        value: Term,
    ) -> Result<(Term, LocalCtx, Vec<Constraint>)> {
        let new_time_var = ctx.gen_new_var(DEFAULT_TIME_VAR);
        let new_time_term = ctx.insert_declared_var(&new_time_var, Type::Int)?;
        Ok((
            Term::Pair(new_time_term.clone().into(), value.into()),
            LocalCtx {
                error_var: lctx.error_var.clone(),
                time_var: new_time_term.clone(),
            },
            vec![Constraint::Le(lctx.time_var.clone(), new_time_term)],
        ))
    }

    fn recv_lctx<P: LoweringPolicy>(ctx: &mut Ctx<P>, lctx: &LocalCtx) -> Result<LocalCtx> {
        let new_time_var = ctx.gen_new_var(DEFAULT_TIME_VAR);
        let new_time_term = ctx.insert_declared_var(&new_time_var, Type::Int)?;
        Ok(LocalCtx {
            error_var: lctx.error_var.clone(),
            time_var: new_time_term,
        })
    }

    fn recv_item_and_constraints<P: LoweringPolicy>(
        ctx: &mut Ctx<P>,
        lctx: &LocalCtx,
        recv_lctx: &LocalCtx,
        value: Term,
    ) -> Result<(Term, Vec<Constraint>)> {
        let tmp_time_var = ctx.gen_new_var(DEFAULT_TIME_VAR);
        let tmp_time_term = ctx.insert_declared_var(&tmp_time_var, Type::Int)?;
        Ok((
            Term::Pair(tmp_time_term.clone().into(), value.into()),
            vec![
                Constraint::Lt(tmp_time_term, recv_lctx.time_var.clone()),
                Constraint::Le(lctx.time_var.clone(), recv_lctx.time_var.clone()),
            ],
        ))
    }
}

impl TimeEncoding for Untimestamped {
    fn channel_item_type(payload_ty: Type) -> Type {
        payload_ty
    }

    fn predicate_arg_types(status_ty: Type) -> Vec<Type> {
        vec![status_ty]
    }

    fn channel_item_value(item: Term) -> Term {
        item
    }

    fn predicate_args(status: Term, _time: Term) -> Vec<Term> {
        vec![status]
    }

    fn sorted_new_predicates(
        _sorted_predicate: PredicateName,
        _sender: Term,
    ) -> Vec<PredicateAtom> {
        vec![]
    }

    fn sorted_primitive_clauses(
        _sorted_predicate: PredicateName,
        _prophecy_ty: Type,
    ) -> Vec<Clause> {
        vec![]
    }

    fn initial_time_var<P: LoweringPolicy>(_ctx: &mut Ctx<P>) -> Result<Term> {
        Ok(Term::Var(DEFAULT_TIME_VAR.to_string()))
    }

    fn send_item_and_lctx<P: LoweringPolicy>(
        _ctx: &mut Ctx<P>,
        lctx: &LocalCtx,
        value: Term,
    ) -> Result<(Term, LocalCtx, Vec<Constraint>)> {
        Ok((value, lctx.clone(), vec![]))
    }

    fn recv_lctx<P: LoweringPolicy>(_ctx: &mut Ctx<P>, lctx: &LocalCtx) -> Result<LocalCtx> {
        Ok(lctx.clone())
    }

    fn recv_item_and_constraints<P: LoweringPolicy>(
        _ctx: &mut Ctx<P>,
        _lctx: &LocalCtx,
        _recv_lctx: &LocalCtx,
        value: Term,
    ) -> Result<(Term, Vec<Constraint>)> {
        Ok((value, vec![]))
    }
}

impl CheckEncoding for FailReachabilityCheck {
    fn status_type() -> Type {
        Type::Bool
    }

    fn status(status: CheckStatus) -> Term {
        match status {
            CheckStatus::Failure | CheckStatus::InitQuery => Term::Bool(true),
            CheckStatus::Terminated => Term::Bool(false),
            CheckStatus::Blocked => unreachable!("fail reachability does not use blocked status"),
        }
    }

    fn unit_body<P: LoweringPolicy>(_ctx: &mut Ctx<P>, _lctx: &LocalCtx) -> Result<Option<Body>> {
        Ok(None)
    }

    fn spawn_status_bodies(
        parent_error: Term,
        first_error: Term,
        second_error: Term,
    ) -> DisjunctiveBody {
        vec![Body {
            predicates: vec![],
            constraints: vec![Constraint::Eq(
                parent_error,
                Term::LOr(Box::new(first_error), Box::new(second_error)),
            )],
        }]
    }

    fn recv_blocked_body<P: LoweringPolicy>(
        _ctx: &mut Ctx<P>,
        _lctx: &LocalCtx,
        _receiver_term: Term,
        _receiver_ty: Type,
        _type_env_before_recv: HashMap<ast::VarName, ast::Type>,
    ) -> Result<Option<Body>> {
        Ok(None)
    }

    fn synthetic_termination_clause<P: LoweringPolicy>(
        ctx: &mut Ctx<P>,
        name: &str,
        time_var: Term,
        param_terms: &[Term],
    ) -> Result<Option<Clause>> {
        Ok(Some(Clause {
            forall: ctx.var_declarations.clone().into_iter().collect(),
            head: Some(PredicateAtom {
                name: name.to_string(),
                args: [
                    Term::predicate_args_for_policy::<P>(
                        Self::status(CheckStatus::Terminated),
                        time_var,
                    ),
                    param_terms.to_vec(),
                ]
                .concat(),
            }),
            body: ctx.terminal_closed_body()?,
        }))
    }
}

impl CheckEncoding for DeadlockFreedomCheck {
    fn status_type() -> Type {
        Type::Int
    }

    fn status(status: CheckStatus) -> Term {
        match status {
            CheckStatus::Failure => status_fail(),
            CheckStatus::Terminated => status_terminated(),
            CheckStatus::InitQuery | CheckStatus::Blocked => status_blocked(),
        }
    }

    fn unit_body<P: LoweringPolicy>(ctx: &mut Ctx<P>, lctx: &LocalCtx) -> Result<Option<Body>> {
        let mut body = ctx.terminal_closed_body()?;
        body.constraints.push(Constraint::Eq(
            lctx.error_var.clone(),
            Self::status(CheckStatus::Terminated),
        ));
        Ok(Some(body))
    }

    fn spawn_status_bodies(
        parent_error: Term,
        first_error: Term,
        second_error: Term,
    ) -> DisjunctiveBody {
        vec![
            Body {
                predicates: vec![],
                constraints: vec![
                    Constraint::Le(first_error.clone(), second_error.clone()),
                    Constraint::Eq(parent_error.clone(), first_error.clone()),
                ],
            },
            Body {
                predicates: vec![],
                constraints: vec![
                    Constraint::Le(second_error.clone(), first_error),
                    Constraint::Eq(parent_error, second_error),
                ],
            },
        ]
    }

    fn recv_blocked_body<P: LoweringPolicy>(
        ctx: &mut Ctx<P>,
        lctx: &LocalCtx,
        receiver_term: Term,
        receiver_ty: Type,
        type_env_before_recv: HashMap<ast::VarName, ast::Type>,
    ) -> Result<Option<Body>> {
        let type_env_after_recv = std::mem::replace(&mut ctx.type_env, type_env_before_recv);
        let mut blocked_body = ctx.terminal_closed_body()?;
        ctx.type_env = type_env_after_recv;
        blocked_body.constraints.extend([
            Constraint::Eq(receiver_term, Term::Nil(receiver_ty)),
            Constraint::Eq(lctx.error_var.clone(), Self::status(CheckStatus::Blocked)),
        ]);
        Ok(Some(blocked_body))
    }

    fn synthetic_termination_clause<P: LoweringPolicy>(
        _ctx: &mut Ctx<P>,
        _name: &str,
        _time_var: Term,
        _param_terms: &[Term],
    ) -> Result<Option<Clause>> {
        Ok(None)
    }
}

impl Type {
    fn prophecy_for_policy<P: LoweringPolicy>(payload_ty: Type) -> Type {
        Type::Lst(Box::new(P::Time::channel_item_type(payload_ty)))
    }

    fn channel_item_for_policy<P: LoweringPolicy>(payload_ty: Type) -> Type {
        P::Time::channel_item_type(payload_ty)
    }

    fn predicate_args_for_policy<P: LoweringPolicy>(status_ty: Type) -> Vec<Type> {
        P::Time::predicate_arg_types(status_ty)
    }
}

impl Term {
    fn channel_item_value_for_policy<P: LoweringPolicy>(item: Term) -> Term {
        P::Time::channel_item_value(item)
    }

    fn predicate_args_for_policy<P: LoweringPolicy>(status: Term, time: Term) -> Vec<Term> {
        P::Time::predicate_args(status, time)
    }
}

impl PredicateAtom {
    fn sorted_new_for_policy<P: LoweringPolicy>(
        sorted_predicate: PredicateName,
        sender: Term,
    ) -> Vec<Self> {
        P::Time::sorted_new_predicates(sorted_predicate, sender)
    }
}

impl Clause {
    fn sorted_primitive_clauses_for_policy<P: LoweringPolicy>(
        sorted_predicate: PredicateName,
        prophecy_ty: Type,
    ) -> Vec<Self> {
        P::Time::sorted_primitive_clauses(sorted_predicate, prophecy_ty)
    }
}

impl Body {
    fn spawn_bodies_for_policy<P: LoweringPolicy>(
        parent_error: Term,
        first_error: Term,
        second_error: Term,
        body: Body,
    ) -> DisjunctiveBody {
        P::Check::spawn_status_bodies(parent_error, first_error, second_error)
            .into_iter()
            .map(|status_body| status_body.concat(body.clone()))
            .collect()
    }
}

#[derive(Debug)]
struct Ctx<P: LoweringPolicy> {
    var_declarations: HashMap<PredicateName, Type>,
    fun_declarations: HashMap<PredicateName, Vec<Type>>,
    type_env: HashMap<ast::VarName, ast::Type>,
    adts: HashMap<ast::TypeName, ast::AdtDef>,
    primitive_payload_types: Vec<Type>,
    closed_payload_types: Vec<ast::Type>,
    closed_value_types: Vec<ast::Type>,
    unused_num: usize,
    _policy: PhantomData<P>,
}

impl<P: LoweringPolicy> Default for Ctx<P> {
    fn default() -> Self {
        Self {
            var_declarations: HashMap::new(),
            fun_declarations: HashMap::new(),
            type_env: HashMap::new(),
            adts: HashMap::new(),
            primitive_payload_types: Vec::new(),
            closed_payload_types: Vec::new(),
            closed_value_types: Vec::new(),
            unused_num: 0,
            _policy: PhantomData,
        }
    }
}

impl<P: LoweringPolicy> Ctx<P> {
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

    fn initial_time_var(&mut self) -> Result<Term> {
        P::Time::initial_time_var(self)
    }

    fn send_item_and_lctx(
        &mut self,
        lctx: &LocalCtx,
        value: Term,
    ) -> Result<(Term, LocalCtx, Vec<Constraint>)> {
        P::Time::send_item_and_lctx(self, lctx, value)
    }

    fn recv_lctx(&mut self, lctx: &LocalCtx) -> Result<LocalCtx> {
        P::Time::recv_lctx(self, lctx)
    }

    fn recv_item_and_constraints(
        &mut self,
        lctx: &LocalCtx,
        recv_lctx: &LocalCtx,
        value: Term,
    ) -> Result<(Term, Vec<Constraint>)> {
        P::Time::recv_item_and_constraints(self, lctx, recv_lctx, value)
    }

    fn unit_bodies(&mut self, lctx: &LocalCtx) -> Result<DisjunctiveBody> {
        Ok(P::Check::unit_body(self, lctx)?.into_iter().collect())
    }

    fn recv_bodies(
        &mut self,
        lctx: &LocalCtx,
        normal_body: Body,
        receiver_term: Term,
        receiver_ty: Type,
        type_env_before_recv: HashMap<ast::VarName, ast::Type>,
    ) -> Result<DisjunctiveBody> {
        let blocked_body = P::Check::recv_blocked_body(
            self,
            lctx,
            receiver_term,
            receiver_ty,
            type_env_before_recv,
        )?;
        Ok(std::iter::once(normal_body).chain(blocked_body).collect())
    }

    fn synthetic_termination_clauses(
        &mut self,
        name: &str,
        time_var: Term,
        param_terms: &[Term],
    ) -> Result<Vec<Clause>> {
        Ok(
            P::Check::synthetic_termination_clause(self, name, time_var, param_terms)?
                .into_iter()
                .collect(),
        )
    }

    fn ensure_primitive_payload(&mut self, payload_ty: Type) {
        if !self.primitive_payload_types.contains(&payload_ty) {
            self.primitive_payload_types.push(payload_ty.clone());
        }
        self.fun_declarations
            .extend(CHC::primitive_fun_declarations_for_policy::<P>(payload_ty));
    }

    fn primitive_predicates_for_payload(
        &mut self,
        payload_ty: Type,
    ) -> (PredicateName, PredicateName) {
        self.ensure_primitive_payload(payload_ty.clone());
        CHC::primitive_predicate_names(&payload_ty)
    }

    fn ensure_closed_payload(&mut self, payload: ast::Type) -> Result<PredicateName> {
        let name = payload.closed_predicate_name();
        if !self.closed_payload_types.contains(&payload) {
            let predicate_ty = payload.closed_list_type::<P>()?;
            self.closed_payload_types.push(payload.clone());
            self.fun_declarations
                .insert(name.clone(), vec![predicate_ty]);
            if let ast::Type::Receiver(inner) = &payload {
                if inner.needs_closed_value() {
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
                body.constraints
                    .push(Constraint::Eq(term, Term::Nil(ty.lower_to_chc::<P>()?)));
            }
            ast::Type::Receiver(payload) if payload.needs_closed_value() => {
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
        let name = ty.closed_value_predicate_name();
        if !self.closed_value_types.contains(&ty) {
            let chc_ty = ty.lower_to_chc::<P>()?;
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
                            ast::Type::Receiver(payload) if payload.needs_closed_value() => {
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
            let term = self.insert_declared_var(var, ty.lower_to_chc::<P>()?)?;
            self.add_closed_value_conditions(&mut body, term, &ty)?;
        }
        Ok(body)
    }

    fn closed_clauses_for_payload(&mut self, payload: &ast::Type) -> Result<Vec<Clause>> {
        let predicate_name = payload.closed_predicate_name();
        let list_ty = payload.closed_list_type::<P>()?;
        let item_ty = Type::channel_item_for_policy::<P>(payload.lower_to_chc::<P>()?);
        let value_term = Term::channel_item_value_for_policy::<P>(Term::Var("p".to_string()));
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
        let predicate_name = ty.closed_value_predicate_name();
        let adt = self
            .adts
            .get(type_name)
            .ok_or_else(|| anyhow::anyhow!("unknown ADT type {}", type_name))?
            .clone();
        let value_ty = ty.lower_to_chc::<P>()?;
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
                        name: DatatypeVariant::constructor_name(type_name, &variant.name),
                        args: field_terms.clone(),
                    },
                )],
            };
            for (term, field_ty) in field_terms.iter().cloned().zip(&variant.fields) {
                self.add_closed_value_conditions(&mut body, term, field_ty)?;
            }
            let mut forall = vec![("v".to_string(), value_ty.clone())];
            for (index, field_ty) in variant.fields.iter().enumerate() {
                forall.push((format!("field{}", index), field_ty.lower_to_chc::<P>()?));
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

impl CHC {
    fn primitive_fun_declarations_for_policy<P: LoweringPolicy>(
        payload_ty: Type,
    ) -> HashMap<PredicateName, Vec<Type>> {
        let prophecy_ty = Type::prophecy_for_policy::<P>(payload_ty.clone());
        let (sorted_predicate, merge_predicate) = CHC::primitive_predicate_names(&payload_ty);
        HashMap::from([
            (sorted_predicate, vec![prophecy_ty.clone()]),
            (
                merge_predicate,
                vec![
                    prophecy_ty.clone(),
                    prophecy_ty.clone(),
                    prophecy_ty.clone(),
                ],
            ),
        ])
    }

    fn primitive_clauses_for_policy<P: LoweringPolicy>(payload_ty: Type) -> Vec<Clause> {
        let prophecy_ty = Type::prophecy_for_policy::<P>(payload_ty.clone());
        let item_ty = Type::channel_item_for_policy::<P>(payload_ty.clone());
        let (sorted_predicate, merge_predicate) = CHC::primitive_predicate_names(&payload_ty);
        let mut clauses =
            Clause::sorted_primitive_clauses_for_policy::<P>(sorted_predicate, prophecy_ty.clone());

        clauses.extend([
            Clause {
                forall: vec![("l".to_string(), prophecy_ty.clone())],
                head: Some(PredicateAtom {
                    name: merge_predicate.clone(),
                    args: vec![
                        Term::Var("l".to_string()),
                        Term::Nil(prophecy_ty.clone()),
                        Term::Var("l".to_string()),
                    ],
                }),
                body: Body::default(),
            },
            Clause {
                forall: vec![("l".to_string(), prophecy_ty.clone())],
                head: Some(PredicateAtom {
                    name: merge_predicate.clone(),
                    args: vec![
                        Term::Nil(prophecy_ty.clone()),
                        Term::Var("l".to_string()),
                        Term::Var("l".to_string()),
                    ],
                }),
                body: Body::default(),
            },
            Clause {
                forall: vec![
                    ("l1".to_string(), prophecy_ty.clone()),
                    ("l2".to_string(), prophecy_ty.clone()),
                    ("l3".to_string(), prophecy_ty.clone()),
                    ("l1tail".to_string(), prophecy_ty.clone()),
                    ("l3tail".to_string(), prophecy_ty.clone()),
                    ("p".to_string(), item_ty.clone()),
                ],
                head: Some(PredicateAtom {
                    name: merge_predicate.clone(),
                    args: vec![
                        Term::Var("l1".to_string()),
                        Term::Var("l2".to_string()),
                        Term::Var("l3".to_string()),
                    ],
                }),
                body: Body {
                    predicates: vec![PredicateAtom {
                        name: merge_predicate.clone(),
                        args: vec![
                            Term::Var("l1tail".to_string()),
                            Term::Var("l2".to_string()),
                            Term::Var("l3tail".to_string()),
                        ],
                    }],
                    constraints: vec![
                        Constraint::Eq(
                            Term::Var("l1".to_string()),
                            Term::Cons(
                                Term::Var("p".to_string()).into(),
                                Term::Var("l1tail".to_string()).into(),
                            ),
                        ),
                        Constraint::Eq(
                            Term::Var("l3".to_string()),
                            Term::Cons(
                                Term::Var("p".to_string()).into(),
                                Term::Var("l3tail".to_string()).into(),
                            ),
                        ),
                    ],
                },
            },
            Clause {
                forall: vec![
                    ("l1".to_string(), prophecy_ty.clone()),
                    ("l2".to_string(), prophecy_ty.clone()),
                    ("l3".to_string(), prophecy_ty.clone()),
                    ("l2tail".to_string(), prophecy_ty.clone()),
                    ("l3tail".to_string(), prophecy_ty),
                    ("p".to_string(), item_ty),
                ],
                head: Some(PredicateAtom {
                    name: merge_predicate.clone(),
                    args: vec![
                        Term::Var("l1".to_string()),
                        Term::Var("l2".to_string()),
                        Term::Var("l3".to_string()),
                    ],
                }),
                body: Body {
                    predicates: vec![PredicateAtom {
                        name: merge_predicate,
                        args: vec![
                            Term::Var("l1".to_string()),
                            Term::Var("l2tail".to_string()),
                            Term::Var("l3tail".to_string()),
                        ],
                    }],
                    constraints: vec![
                        Constraint::Eq(
                            Term::Var("l2".to_string()),
                            Term::Cons(
                                Term::Var("p".to_string()).into(),
                                Term::Var("l2tail".to_string()).into(),
                            ),
                        ),
                        Constraint::Eq(
                            Term::Var("l3".to_string()),
                            Term::Cons(
                                Term::Var("p".to_string()).into(),
                                Term::Var("l3tail".to_string()).into(),
                            ),
                        ),
                    ],
                },
            },
        ]);

        clauses
    }
}

impl Datatype {
    fn adt_type_name(name: &str) -> String {
        format!("Adt${}", name)
    }
}

impl DatatypeVariant {
    fn constructor_name(type_name: &str, variant: &str) -> String {
        format!("Adt${}${}", type_name, variant)
    }

    fn selector_name(type_name: &str, variant: &str, index: usize) -> String {
        format!("Adt${}${}${}", type_name, variant, index)
    }
}

impl ast::AdtDef {
    fn lower_to_chc<P: LoweringPolicy>(&self) -> Result<Datatype> {
        let variants = self
            .variants
            .iter()
            .map(|variant| {
                let fields = variant
                    .fields
                    .iter()
                    .enumerate()
                    .map(|(index, ty)| {
                        Ok((
                            DatatypeVariant::selector_name(&self.name, &variant.name, index),
                            ty.lower_to_chc::<P>()?,
                        ))
                    })
                    .collect::<Result<Vec<_>>>()?;
                Ok(DatatypeVariant {
                    name: DatatypeVariant::constructor_name(&self.name, &variant.name),
                    fields,
                })
            })
            .collect::<Result<Vec<_>>>()?;
        Ok(Datatype {
            name: Datatype::adt_type_name(&self.name),
            variants,
        })
    }
}

#[derive(Debug, Clone)]
pub struct LocalCtx {
    pub error_var: Term,
    pub time_var: Term,
}

impl ast::Type {
    fn chc_predicate_suffix(&self) -> String {
        match self {
            ast::Type::Int => "Int".to_string(),
            ast::Type::Adt(name) => format!("Adt_{}", name),
            ast::Type::Sender(payload) => format!("Sender_{}", payload.chc_predicate_suffix()),
            ast::Type::Receiver(payload) => {
                format!("Receiver_{}", payload.chc_predicate_suffix())
            }
            ast::Type::Func { params } => {
                let params = params
                    .iter()
                    .map(ast::Type::chc_predicate_suffix)
                    .collect::<Vec<_>>()
                    .join("_");
                format!("Func_{}", params)
            }
        }
    }

    fn closed_predicate_name(&self) -> PredicateName {
        format!("{}${}", CLOSED_PREDICATE, self.chc_predicate_suffix())
    }

    fn closed_value_predicate_name(&self) -> PredicateName {
        format!("{}Value${}", CLOSED_PREDICATE, self.chc_predicate_suffix())
    }

    fn needs_closed_value(&self) -> bool {
        match self {
            ast::Type::Sender(_) => true,
            ast::Type::Receiver(payload) => payload.needs_closed_value(),
            ast::Type::Adt(_) => true,
            ast::Type::Int | ast::Type::Func { .. } => false,
        }
    }

    fn closed_list_type<P: LoweringPolicy>(&self) -> Result<Type> {
        Ok(Type::prophecy_for_policy::<P>(self.lower_to_chc::<P>()?))
    }

    fn lower_to_chc<P: LoweringPolicy>(&self) -> Result<Type> {
        Ok(match self {
            ast::Type::Int => Type::Int,
            ast::Type::Adt(name) => Type::Adt(Datatype::adt_type_name(name)),
            ast::Type::Sender(payload) | ast::Type::Receiver(payload) => {
                Type::prophecy_for_policy::<P>(payload.lower_to_chc::<P>()?)
            }
            ast::Type::Func { params } => {
                let chc_params = params
                    .iter()
                    .map(|p| p.lower_to_chc::<P>())
                    .collect::<Result<Vec<_>>>()?;
                Type::Func { args: chc_params }
            }
        })
    }
}

impl ast::Expr {
    fn lower_to_chc<P: LoweringPolicy>(&self, ctx: &mut Ctx<P>) -> Result<Term> {
        Ok(match self {
            ast::Expr::Num(n) => Term::Int(*n),
            ast::Expr::Var(var) => {
                let ast_ty = ctx.get_ast_type(var)?.clone();
                let chc_ty = ast_ty.lower_to_chc::<P>()?;
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
                    name: DatatypeVariant::constructor_name(type_name, variant),
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
    fn lower_to_chc<P: LoweringPolicy>(&self, ctx: &mut Ctx<P>, lctx: &LocalCtx) -> Result<Body> {
        let ast::FuncCall { name, args } = self;
        let error_var = lctx.error_var.clone();
        let time_var = lctx.time_var.clone();
        let default_args = Term::predicate_args_for_policy::<P>(error_var, time_var);
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
    fn lower_to_chc<P: LoweringPolicy>(
        &self,
        ctx: &mut Ctx<P>,
        lctx: &LocalCtx,
    ) -> Result<DisjunctiveBody> {
        Ok(match self {
            ast::Statement::Unit => ctx.unit_bodies(lctx)?,

            ast::Statement::Fail => {
                let mut body = ctx.terminal_closed_body()?;
                let error_var = lctx.error_var.clone();
                body.constraints.push(Constraint::Eq(
                    error_var,
                    P::Check::status(CheckStatus::Failure),
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
                let first_error_term =
                    ctx.insert_declared_var(&first_error_var, P::Check::status_type())?;
                let second_error_var = ctx.gen_new_var(DEFAULT_ERROR_VAR);
                let second_error_term =
                    ctx.insert_declared_var(&second_error_var, P::Check::status_type())?;

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
                Body::spawn_bodies_for_policy::<P>(
                    lctx.error_var.clone(),
                    first_error_term,
                    second_error_term,
                    spawned_body,
                )
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
                let payload_chc_ty = payload.lower_to_chc::<P>()?;
                let sender_var = ctx.insert_declared_var(sender, sender_ty.lower_to_chc::<P>()?)?;
                let receiver_var =
                    ctx.insert_declared_var(receiver, receiver_ty.lower_to_chc::<P>()?)?;
                let (sorted_predicate, _) = ctx.primitive_predicates_for_payload(payload_chc_ty);
                let body = body.lower_to_chc(ctx, lctx)?;
                vec![body.concat(Body {
                    predicates: PredicateAtom::sorted_new_for_policy::<P>(
                        sorted_predicate,
                        sender_var.clone(),
                    ),
                    constraints: vec![Constraint::Eq(receiver_var, sender_var)],
                })]
            }
            ast::Statement::Send {
                sender,
                value,
                body,
            } => {
                let sender_ty = ctx.get_ast_type(sender)?.clone();
                let sender_chc_ty = sender_ty.lower_to_chc::<P>()?;
                let sender_var = ctx.insert_declared_var(sender, sender_chc_ty.clone())?;
                let value_term = value.lower_to_chc(ctx)?;
                let (item_term, new_lctx, time_constraints) =
                    ctx.send_item_and_lctx(lctx, value_term)?;
                let mut body = body.lower_to_chc(ctx, &new_lctx)?;
                let new_sender = ctx.gen_new_var(sender);
                let new_sender_var = ctx.insert_declared_var(&new_sender, sender_chc_ty)?;
                body.substitute(&HashMap::from([(sender.clone(), new_sender)]));
                let mut constraints = vec![Constraint::Eq(
                    sender_var,
                    Term::Cons(item_term.into(), new_sender_var.into()),
                )];
                constraints.extend(time_constraints);
                vec![body.concat(Body {
                    predicates: vec![],
                    constraints,
                })]
            }
            ast::Statement::Recv {
                receiver,
                var,
                body,
            } => {
                let type_env_before_recv = ctx.type_env.clone();
                let receiver_ty = ctx.get_ast_type(receiver)?.clone();
                let payload_ty = receiver_ty
                    .payload()
                    .cloned()
                    .ok_or_else(|| anyhow::anyhow!("Variable {} is not a receiver", receiver))?;
                ctx.type_env.insert(var.clone(), payload_ty.clone());
                let recv_lctx = ctx.recv_lctx(lctx)?;
                let mut body = body.lower_to_chc(ctx, &recv_lctx)?;
                let receiver_chc_ty = receiver_ty.lower_to_chc::<P>()?;
                let var_term = ctx.insert_declared_var(var, payload_ty.lower_to_chc::<P>()?)?;
                let (item_term, time_constraints) =
                    ctx.recv_item_and_constraints(lctx, &recv_lctx, var_term)?;
                let receiver_term = ctx.insert_declared_var(receiver, receiver_chc_ty.clone())?;
                let new_receiver = ctx.gen_new_var(receiver);
                let new_receiver_term =
                    ctx.insert_declared_var(&new_receiver, receiver_chc_ty.clone())?;
                body.substitute(&HashMap::from([(receiver.clone(), new_receiver)]));

                let normal_body = Body {
                    predicates: vec![],
                    constraints: vec![Constraint::Eq(
                        receiver_term.clone(),
                        Term::Cons(item_term.into(), new_receiver_term.clone().into()),
                    )],
                }
                .concat(Body {
                    predicates: vec![],
                    constraints: time_constraints,
                })
                .concat(body);

                ctx.recv_bodies(
                    lctx,
                    normal_body,
                    receiver_term,
                    receiver_chc_ty,
                    type_env_before_recv,
                )?
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
                let scrutinee_chc_ty = scrutinee_ty.lower_to_chc::<P>()?;
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
                            ctx.insert_declared_var(fresh_var, field_ty.lower_to_chc::<P>()?)
                        })
                        .collect::<Result<Vec<_>>>()?;
                    bodies.push(
                        Body {
                            predicates: vec![],
                            constraints: vec![Constraint::Eq(
                                scrutinee_term.clone(),
                                Term::Ctor {
                                    name: DatatypeVariant::constructor_name(
                                        type_name,
                                        &arm.variant,
                                    ),
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
                    ctx.primitive_predicates_for_payload(payload_ty.lower_to_chc::<P>()?);
                let sender_chc_ty = sender_ty.lower_to_chc::<P>()?;
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
    fn lower_to_chc<P: LoweringPolicy>(&self, ctx: &mut Ctx<P>) -> Result<Vec<Clause>> {
        let mut clauses = vec![];
        let error_var = ctx.insert_declared_var(DEFAULT_ERROR_VAR, P::Check::status_type())?;
        let time_var = ctx.initial_time_var()?;

        for (param_name, param_type) in &self.params {
            let chc_type = param_type.lower_to_chc::<P>()?;
            ctx.insert_to_type_env(param_name, param_type.clone())?;
            ctx.insert_declared_var(param_name.clone(), chc_type)?;
        }

        let param_terms: Vec<Term> = self
            .params
            .iter()
            .map(|(param_name, _)| Term::Var(param_name.clone()))
            .collect::<Vec<Term>>();

        clauses.extend(ctx.synthetic_termination_clauses(
            &self.name,
            time_var.clone(),
            &param_terms,
        )?);

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
                        Term::predicate_args_for_policy::<P>(error_var.clone(), time_var.clone()),
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
        if setting.no_timestamps {
            self.lower_to_chc_with_time::<Untimestamped>(setting)
        } else {
            self.lower_to_chc_with_time::<Timestamped>(setting)
        }
    }

    fn lower_to_chc_with_time<T: TimeEncoding>(&self, setting: Setting) -> Result<CHC> {
        match setting.check_mode {
            CheckMode::FailReachability => {
                self.lower_to_chc_with_policy::<Policy<T, FailReachabilityCheck>>(setting)
            }
            CheckMode::DeadlockFreedom => {
                self.lower_to_chc_with_policy::<Policy<T, DeadlockFreedomCheck>>(setting)
            }
        }
    }

    fn lower_to_chc_with_policy<P: LoweringPolicy>(&self, setting: Setting) -> Result<CHC> {
        let mut chc = CHC::init_premitive(&setting);
        chc.datatypes = self
            .adts
            .iter()
            .map(ast::AdtDef::lower_to_chc::<P>)
            .collect::<Result<Vec<_>>>()?;
        let mut ctx: Ctx<P> = Ctx {
            fun_declarations: chc.fun_declarations.clone(),
            adts: self
                .adts
                .iter()
                .map(|adt| (adt.name.clone(), adt.clone()))
                .collect(),
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
                let mut params = Type::predicate_args_for_policy::<P>(P::Check::status_type());
                params.extend(
                    func.params
                        .iter()
                        .map(|(_, ty)| ty.lower_to_chc::<P>())
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

        let time_var = ctx.initial_time_var()?;
        let init_query_status = P::Check::status(CheckStatus::InitQuery);

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
                .extend(CHC::primitive_clauses_for_policy::<P>(payload_ty));
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
            setting,
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
    fn setting_dispatch_selects_time_and_check_axes_independently() {
        let program = parser::parse_program(
            r#"
            init = main()

            main() = new s, r in done(s, r)
            done(s: Sender, r: Receiver) = ()
            "#,
        )
        .expect("program should parse");
        let timestamped_channel = Type::Lst(Box::new(Type::timestamped_value(Type::Int)));
        let untimestamped_channel = Type::Lst(Box::new(Type::Int));

        let timestamped_fail = program
            .lower_to_chc(Setting {
                no_timestamps: false,
                check_mode: CheckMode::FailReachability,
            })
            .expect("program should lower");
        assert_eq!(
            timestamped_fail.fun_declarations["done"],
            vec![
                Type::Bool,
                Type::Int,
                timestamped_channel.clone(),
                timestamped_channel.clone()
            ]
        );

        let untimestamped_fail = program
            .lower_to_chc(Setting {
                no_timestamps: true,
                check_mode: CheckMode::FailReachability,
            })
            .expect("program should lower");
        assert_eq!(
            untimestamped_fail.fun_declarations["done"],
            vec![
                Type::Bool,
                untimestamped_channel.clone(),
                untimestamped_channel.clone()
            ]
        );

        let timestamped_deadlock = program
            .lower_to_chc(Setting {
                no_timestamps: false,
                check_mode: CheckMode::DeadlockFreedom,
            })
            .expect("program should lower");
        assert_eq!(
            timestamped_deadlock.fun_declarations["done"],
            vec![
                Type::Int,
                Type::Int,
                timestamped_channel.clone(),
                timestamped_channel
            ]
        );

        let untimestamped_deadlock = program
            .lower_to_chc(Setting {
                no_timestamps: true,
                check_mode: CheckMode::DeadlockFreedom,
            })
            .expect("program should lower");
        assert_eq!(
            untimestamped_deadlock.fun_declarations["done"],
            vec![
                Type::Int,
                untimestamped_channel.clone(),
                untimestamped_channel
            ]
        );
    }

    #[test]
    fn no_timestamp_send_and_recv_do_not_allocate_fresh_time_vars() {
        let program = parser::parse_program(
            r#"
            init = main()

            main() = new s, r in write(s, r)
            write(s: Sender, r: Receiver) = send 1 to s; read(s, r)
            read(s: Sender, r: Receiver) = let v = recv r in done(s, r, v)
            done(s: Sender, r: Receiver, v: int) = fail
            "#,
        )
        .expect("program should parse");

        let timestamped = program
            .lower_to_chc(Setting {
                no_timestamps: false,
                check_mode: CheckMode::FailReachability,
            })
            .expect("program should lower");
        assert!(
            timestamped
                .clauses
                .iter()
                .any(|clause| { clause.forall.iter().any(|(var, _)| var.starts_with("%t%")) }),
            "timestamped lowering should allocate fresh time variables"
        );

        let untimestamped = program
            .lower_to_chc(Setting {
                no_timestamps: true,
                check_mode: CheckMode::FailReachability,
            })
            .expect("program should lower");
        assert!(
            !untimestamped
                .clauses
                .iter()
                .any(|clause| { clause.forall.iter().any(|(var, _)| var.starts_with("%t")) }),
            "untimestamped lowering should not declare time variables"
        );
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

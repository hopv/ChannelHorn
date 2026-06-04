use std::collections::{BTreeSet, HashMap};

use anyhow::{Result, bail};

use crate::core::ast as core;

use super::ast::{self, AssignOp, BinaryOp, Expr, MethodCall, Stmt, VarName};

const ENTRY_FUNC: &str = "__sugar_entry";
const UNIT_FUNC: &str = "__sugar_unit";
const FAIL_FUNC: &str = "__sugar_fail";

#[derive(Debug, Clone)]
struct Env {
    vars: Vec<(VarName, core::Type)>,
}

impl Env {
    fn new() -> Self {
        Self { vars: vec![] }
    }

    fn insert(&mut self, var: VarName, ty: core::Type) {
        if let Some((_, existing_ty)) = self.vars.iter_mut().find(|(name, _)| name == &var) {
            *existing_ty = ty;
        } else {
            self.vars.push((var, ty));
        }
    }

    fn remove(&mut self, var: &str) {
        self.vars.retain(|(name, _)| name != var);
    }

    fn get(&self, var: &str) -> Option<&core::Type> {
        self.vars
            .iter()
            .find_map(|(name, ty)| (name == var).then_some(ty))
    }

    fn params_for(&self, live: &BTreeSet<VarName>) -> Vec<(VarName, core::Type)> {
        self.vars
            .iter()
            .filter(|(name, ty)| live.contains(name) || ty.is_linear())
            .cloned()
            .collect()
    }

    fn params_for_live_only(&self, live: &BTreeSet<VarName>) -> Vec<(VarName, core::Type)> {
        self.vars
            .iter()
            .filter(|(name, _)| live.contains(name))
            .cloned()
            .collect()
    }

    fn remove_linear_vars(&mut self, vars: &BTreeSet<VarName>) {
        self.vars
            .retain(|(name, ty)| !vars.contains(name) || !ty.is_linear());
    }

    fn linear_params(&self) -> Vec<(VarName, core::Type)> {
        self.vars
            .iter()
            .filter(|(_, ty)| ty.is_linear())
            .cloned()
            .collect()
    }
}

#[derive(Debug)]
struct Ctx {
    adts: Vec<core::AdtDef>,
    functions: HashMap<core::FuncName, core::Function>,
    next_label: usize,
}

impl Ctx {
    fn with_adts(adts: Vec<core::AdtDef>) -> Self {
        let mut ctx = Self {
            adts,
            functions: HashMap::new(),
            next_label: 0,
        };
        ctx.insert_function(core::Function {
            name: UNIT_FUNC.to_string(),
            params: vec![],
            body: core::Statement::Unit,
        });
        ctx.insert_function(core::Function {
            name: FAIL_FUNC.to_string(),
            params: vec![],
            body: core::Statement::Fail,
        });
        ctx
    }

    fn fresh_label(&mut self) -> core::FuncName {
        let label = format!("__sugar_{}", self.next_label);
        self.next_label += 1;
        label
    }

    fn fresh_var(&mut self) -> VarName {
        let var = format!("__sugar_var_{}", self.next_label);
        self.next_label += 1;
        var
    }

    fn insert_function(&mut self, function: core::Function) {
        self.functions.insert(function.name.clone(), function);
    }
}

pub fn desugar_program(program: &ast::Program) -> Result<core::Program> {
    let liveness = Liveness::new(&program.statements);
    let mut ctx = Ctx::with_adts(program.adts.clone());
    let mut env = Env::new();
    for var in liveness.live_before(0) {
        env.insert(var.clone(), core::Type::Int);
    }
    emit_sequence(
        &mut ctx,
        ENTRY_FUNC.to_string(),
        &program.statements,
        0,
        env,
        &liveness,
    )?;

    Ok(core::Program {
        adts: program.adts.clone(),
        functions: ctx.functions,
        init: core::FuncCall {
            name: ENTRY_FUNC.to_string(),
            args: liveness
                .live_before(0)
                .iter()
                .cloned()
                .map(core::Expr::Var)
                .collect(),
        },
    })
}

fn emit_sequence(
    ctx: &mut Ctx,
    name: core::FuncName,
    statements: &[Stmt],
    index: usize,
    env: Env,
    liveness: &Liveness,
) -> Result<()> {
    let params = if index < statements.len() {
        env.params_for(liveness.live_before(index))
    } else {
        vec![]
    };
    let body = if index < statements.len() {
        desugar_stmt(ctx, statements, index, env, liveness)?
    } else {
        core::Statement::Unit
    };
    ctx.insert_function(core::Function { name, params, body });
    Ok(())
}

fn desugar_stmt(
    ctx: &mut Ctx,
    statements: &[Stmt],
    index: usize,
    env: Env,
    liveness: &Liveness,
) -> Result<core::Statement> {
    let stmt = &statements[index];
    match stmt {
        Stmt::LetChannel {
            payload,
            sender,
            receiver,
        } => {
            let mut next_env = env.clone();
            let sender_ty = core::Type::sender(payload.clone());
            let receiver_ty = core::Type::receiver(payload.clone());
            next_env.insert(sender.clone(), sender_ty);
            next_env.insert(receiver.clone(), receiver_ty);
            let body = continuation_call(ctx, statements, index, next_env, liveness, &[])?;
            Ok(core::Statement::New {
                payload: payload.clone(),
                sender: sender.clone(),
                receiver: receiver.clone(),
                body,
            })
        }
        Stmt::Let { binding, value } => match value {
            Expr::MethodCall { receiver, method } if matches!(method, MethodCall::Recv) => {
                let receiver = expect_var(receiver)?;
                let mut next_env = env.clone();
                let payload = ensure_receiver_payload(&next_env, receiver)?.clone();
                next_env.insert(binding.var.clone(), payload);
                let body = continuation_call(ctx, statements, index, next_env, liveness, &[])?;
                Ok(core::Statement::Recv {
                    receiver: receiver.clone(),
                    var: binding.var.clone(),
                    body,
                })
            }
            Expr::MethodCall { receiver, method } if matches!(method, MethodCall::Clone) => {
                let sender = expect_var(receiver)?;
                let mut next_env = env.clone();
                let sender_ty = ensure_sender_type(&next_env, sender)?.clone();
                next_env.insert(binding.var.clone(), sender_ty);
                let body = continuation_call(ctx, statements, index, next_env, liveness, &[])?;
                Ok(core::Statement::Dup {
                    sender: sender.clone(),
                    var: binding.var.clone(),
                    body,
                })
            }
            _ => {
                let value_ty = infer_expr_type(value, &env, ctx)?;
                let value = lower_expr(value)?;
                let mut next_env = env.clone();
                next_env.insert(binding.var.clone(), value_ty);
                remove_linear_free_vars(&mut next_env, value_expr(stmt)?, &env);
                let overrides = [(binding.var.clone(), value)];
                let call =
                    continuation_call(ctx, statements, index, next_env, liveness, &overrides)?;
                Ok(core::Statement::Call(call))
            }
        },
        Stmt::Assign { target, op, value } => {
            if env.get(target).is_some() {
                ensure_type(&env, target, &core::Type::Int)?;
            } else if !matches!(op, AssignOp::Assign) {
                bail!("undefined variable {target}");
            }
            let value = lower_assignment_expr(target, *op, value)?;
            let mut next_env = env.clone();
            next_env.insert(target.clone(), core::Type::Int);
            let overrides = [(target.clone(), value)];
            let call = continuation_call(ctx, statements, index, next_env, liveness, &overrides)?;
            Ok(core::Statement::Call(call))
        }
        Stmt::Expr(expr) => match expr {
            Expr::MethodCall { receiver, method } => match method {
                MethodCall::Send(value) => {
                    let sender = expect_var(receiver)?;
                    let payload = ensure_sender_payload(&env, sender)?;
                    let value_ty = infer_expr_type(value, &env, ctx)?;
                    ensure_type_matches(payload, &value_ty)?;
                    let value_expr = lower_expr(value)?;
                    let mut next_env = env.clone();
                    if value_ty.is_linear() {
                        remove_linear_free_vars(&mut next_env, value, &env);
                    }
                    let body = continuation_call(ctx, statements, index, next_env, liveness, &[])?;
                    Ok(core::Statement::Send {
                        sender: sender.clone(),
                        value: value_expr,
                        body,
                    })
                }
                MethodCall::Drop => {
                    let target = expect_var(receiver)?;
                    let target_ty = ensure_linear(&env, target)?.clone();
                    let mut next_env = env.clone();
                    next_env.remove(target);
                    let continuation =
                        continuation_call(ctx, statements, index, next_env, liveness, &[])?;

                    let drop_name = ctx.fresh_label();
                    ctx.insert_function(core::Function {
                        name: drop_name.clone(),
                        params: vec![(target.clone(), target_ty)],
                        body: core::Statement::Unit,
                    });

                    Ok(core::Statement::Spawn(
                        core::FuncCall {
                            name: drop_name,
                            args: vec![core::Expr::Var(target.clone())],
                        },
                        continuation,
                    ))
                }
                MethodCall::Recv | MethodCall::Clone => {
                    bail!("recv/clone must be used as the right hand side of let")
                }
            },
            _ => bail!("expression statement must be a method call or function call"),
        },
        Stmt::Match { scrutinee, arms } => {
            let type_name = match env.get(scrutinee) {
                Some(core::Type::Adt(type_name)) => type_name.clone(),
                Some(ty) => bail!("expected variable {scrutinee} to be an ADT, got {ty:?}"),
                None => bail!("undefined variable {scrutinee}"),
            };
            let mut continuation_env = env.clone();
            continuation_env.remove(scrutinee);
            let join_call =
                continuation_after_if(ctx, statements, index, continuation_env.clone(), liveness)?;
            let mut core_arms = vec![];
            for arm in arms {
                if arm.type_name != type_name {
                    bail!(
                        "match arm uses ADT '{}', expected '{}'",
                        arm.type_name,
                        type_name
                    );
                }
                let variant = find_variant(ctx, &arm.type_name, &arm.variant)?;
                let mut arm_env = continuation_env.clone();
                for (var, field_ty) in arm.vars.iter().zip(&variant.fields) {
                    arm_env.insert(var.clone(), field_ty.clone());
                }
                core_arms.push(core::MatchArm {
                    type_name: arm.type_name.clone(),
                    variant: arm.variant.clone(),
                    vars: arm.vars.clone(),
                    body: emit_branch_call(ctx, &arm.block, join_call.as_ref(), arm_env)?,
                });
            }
            Ok(core::Statement::Match {
                scrutinee: scrutinee.clone(),
                arms: core_arms,
            })
        }
        Stmt::Call { name, args } => Ok(core::Statement::Call(core::FuncCall {
            name: name.clone(),
            args: args.iter().map(lower_expr).collect::<Result<Vec<_>>>()?,
        })),
        Stmt::Assert(cond) => desugar_assert(ctx, statements, index, env, liveness, cond),
        Stmt::Spawn(block) => {
            let block_liveness = Liveness::new(&block.statements);
            let block_live = block_liveness.live_before(0);
            let spawn_params = env.params_for_live_only(block_live);
            let spawn_env = Env {
                vars: spawn_params.clone(),
            };
            let spawn_name = ctx.fresh_label();
            emit_sequence(
                ctx,
                spawn_name.clone(),
                &block.statements,
                0,
                spawn_env,
                &block_liveness,
            )?;

            let mut continuation_env = env.clone();
            continuation_env.remove_linear_vars(block_live);
            let continuation =
                continuation_call(ctx, statements, index, continuation_env, liveness, &[])?;

            Ok(core::Statement::Spawn(
                core::FuncCall {
                    name: spawn_name,
                    args: spawn_params
                        .into_iter()
                        .map(|(var, _)| core::Expr::Var(var))
                        .collect(),
                },
                continuation,
            ))
        }
        Stmt::If {
            cond,
            then_block,
            else_block,
        } => {
            let join_call = continuation_after_if(ctx, statements, index, env.clone(), liveness)?;
            let then_call = emit_branch_call(ctx, then_block, join_call.as_ref(), env.clone())?;
            let else_call = if let Some(else_block) = else_block {
                emit_branch_call(ctx, else_block, join_call.as_ref(), env)?
            } else {
                join_call.unwrap_or_else(|| terminal_unit_call(ctx, &env))
            };
            Ok(core::Statement::If(lower_expr(cond)?, then_call, else_call))
        }
        Stmt::While { cond, body } => {
            let loop_name = ctx.fresh_label();
            let loop_params = env.params_for(liveness.live_before(index));
            let loop_args = loop_params
                .iter()
                .map(|(var, _)| core::Expr::Var(var.clone()))
                .collect::<Vec<_>>();
            let loop_call = core::FuncCall {
                name: loop_name.clone(),
                args: loop_args,
            };

            let after_call = continuation_call(ctx, statements, index, env, liveness, &[])?;
            let mut body_statements = body.statements.clone();
            body_statements.push(Stmt::Call {
                name: loop_name.clone(),
                args: loop_params
                    .iter()
                    .map(|(var, _)| Expr::Var(var.clone()))
                    .collect(),
            });
            let body_call = emit_statements_call(
                ctx,
                body_statements,
                Env {
                    vars: loop_params.clone(),
                },
            )?;

            ctx.insert_function(core::Function {
                name: loop_name,
                params: loop_params,
                body: core::Statement::If(lower_expr(cond)?, body_call, after_call),
            });

            Ok(core::Statement::Call(loop_call))
        }
    }
}

fn continuation_after_if(
    ctx: &mut Ctx,
    statements: &[Stmt],
    index: usize,
    env: Env,
    liveness: &Liveness,
) -> Result<Option<core::FuncCall>> {
    if index + 1 == statements.len() {
        return Ok(None);
    }

    Ok(Some(continuation_call(
        ctx,
        statements,
        index,
        env,
        liveness,
        &[],
    )?))
}

#[derive(Debug, Clone)]
struct AdtAssert {
    scrutinee: VarName,
    type_name: String,
    variant: String,
    args: Vec<Expr>,
    op: BinaryOp,
}

fn desugar_assert(
    ctx: &mut Ctx,
    statements: &[Stmt],
    index: usize,
    env: Env,
    liveness: &Liveness,
    cond: &Expr,
) -> Result<core::Statement> {
    if let Some(assertion) = adt_assert(cond, &env, ctx)? {
        return desugar_adt_assert(ctx, statements, index, env, liveness, assertion);
    }

    let then_call = continuation_call(ctx, statements, index, env.clone(), liveness, &[])?;
    Ok(core::Statement::If(
        lower_expr(cond)?,
        then_call,
        terminal_fail_call(ctx, &env),
    ))
}

fn adt_assert(cond: &Expr, env: &Env, ctx: &Ctx) -> Result<Option<AdtAssert>> {
    let Expr::BinaryOp { lhs, op, rhs } = cond else {
        return Ok(None);
    };
    if !matches!(op, BinaryOp::Eq | BinaryOp::Ne) {
        return Ok(None);
    }

    let (scrutinee, ctor) = match (&**lhs, &**rhs) {
        (Expr::Var(var), ctor @ Expr::Ctor { .. }) => (var, ctor),
        (ctor @ Expr::Ctor { .. }, Expr::Var(var)) => (var, ctor),
        _ => return Ok(None),
    };
    let Expr::Ctor {
        type_name,
        variant,
        args,
    } = ctor
    else {
        return Ok(None);
    };
    match env.get(scrutinee) {
        Some(core::Type::Adt(actual)) if actual == type_name => {}
        Some(ty) => bail!("expected variable {scrutinee} to be {type_name}, got {ty:?}"),
        None => bail!("undefined variable {scrutinee}"),
    }
    let adt = find_adt(ctx, type_name)?;
    for variant_def in &adt.variants {
        for field in &variant_def.fields {
            if field != &core::Type::Int {
                bail!(
                    "ADT equality is only supported when all fields are int, but '{}::{}' has field {:?}",
                    type_name,
                    variant_def.name,
                    field
                );
            }
        }
    }
    let variant_def = find_variant(ctx, type_name, variant)?;
    if args.len() != variant_def.fields.len() {
        bail!(
            "variant '{}::{}' expects {} fields, got {}",
            type_name,
            variant,
            variant_def.fields.len(),
            args.len()
        );
    }
    Ok(Some(AdtAssert {
        scrutinee: scrutinee.clone(),
        type_name: type_name.clone(),
        variant: variant.clone(),
        args: args.clone(),
        op: *op,
    }))
}

fn desugar_adt_assert(
    ctx: &mut Ctx,
    statements: &[Stmt],
    index: usize,
    env: Env,
    liveness: &Liveness,
    assertion: AdtAssert,
) -> Result<core::Statement> {
    let mut continuation_env = env.clone();
    continuation_env.remove(&assertion.scrutinee);
    let success_call = continuation_call(
        ctx,
        statements,
        index,
        continuation_env.clone(),
        liveness,
        &[],
    )?;
    let failure_call = terminal_fail_call(ctx, &continuation_env);
    let adt = find_adt(ctx, &assertion.type_name)?.clone();
    let mut arms = vec![];

    for variant in adt.variants {
        let vars = (0..variant.fields.len())
            .map(|_| ctx.fresh_var())
            .collect::<Vec<_>>();
        let mut arm_env = continuation_env.clone();
        for (var, field_ty) in vars.iter().zip(&variant.fields) {
            arm_env.insert(var.clone(), field_ty.clone());
        }

        let body = if variant.name == assertion.variant {
            let conds = vars
                .iter()
                .zip(&assertion.args)
                .map(|(var, expected)| {
                    lower_expr(&Expr::BinaryOp {
                        lhs: Box::new(Expr::Var(var.clone())),
                        op: match assertion.op {
                            BinaryOp::Eq => BinaryOp::Eq,
                            BinaryOp::Ne => BinaryOp::Ne,
                            _ => unreachable!("only equality assertions are classified"),
                        },
                        rhs: Box::new(expected.clone()),
                    })
                })
                .collect::<Result<Vec<_>>>()?;
            match assertion.op {
                BinaryOp::Eq => build_all_conditions_call(
                    ctx,
                    conds,
                    success_call.clone(),
                    failure_call.clone(),
                    &arm_env,
                )?,
                BinaryOp::Ne => build_any_condition_call(
                    ctx,
                    conds,
                    success_call.clone(),
                    failure_call.clone(),
                    &arm_env,
                )?,
                _ => unreachable!("only equality assertions are classified"),
            }
        } else {
            match assertion.op {
                BinaryOp::Eq => failure_call.clone(),
                BinaryOp::Ne => success_call.clone(),
                _ => unreachable!("only equality assertions are classified"),
            }
        };

        arms.push(core::MatchArm {
            type_name: assertion.type_name.clone(),
            variant: variant.name,
            vars,
            body,
        });
    }

    Ok(core::Statement::Match {
        scrutinee: assertion.scrutinee,
        arms,
    })
}

fn build_all_conditions_call(
    ctx: &mut Ctx,
    conds: Vec<core::Expr>,
    all_true_call: core::FuncCall,
    any_false_call: core::FuncCall,
    env: &Env,
) -> Result<core::FuncCall> {
    build_condition_chain_call(ctx, conds, all_true_call, any_false_call, env, true)
}

fn build_any_condition_call(
    ctx: &mut Ctx,
    conds: Vec<core::Expr>,
    any_true_call: core::FuncCall,
    all_false_call: core::FuncCall,
    env: &Env,
) -> Result<core::FuncCall> {
    build_condition_chain_call(ctx, conds, any_true_call, all_false_call, env, false)
}

fn build_condition_chain_call(
    ctx: &mut Ctx,
    conds: Vec<core::Expr>,
    true_call: core::FuncCall,
    false_call: core::FuncCall,
    env: &Env,
    require_all: bool,
) -> Result<core::FuncCall> {
    if conds.is_empty() {
        return Ok(if require_all { true_call } else { false_call });
    }

    let live = conds
        .iter()
        .flat_map(core::Expr::free_vars)
        .chain(true_call.free_vars())
        .chain(false_call.free_vars())
        .collect::<BTreeSet<_>>();
    let params = env.params_for(&live);
    let call_args = params
        .iter()
        .map(|(var, _)| core::Expr::Var(var.clone()))
        .collect::<Vec<_>>();
    let mut next_call = if require_all {
        true_call.clone()
    } else {
        false_call.clone()
    };

    for cond in conds.into_iter().rev() {
        let name = ctx.fresh_label();
        let call = core::FuncCall {
            name: name.clone(),
            args: call_args.clone(),
        };
        let body = if require_all {
            core::Statement::If(cond, next_call, false_call.clone())
        } else {
            core::Statement::If(cond, true_call.clone(), next_call)
        };
        ctx.insert_function(core::Function {
            name,
            params: params.clone(),
            body,
        });
        next_call = call;
    }

    Ok(next_call)
}

fn emit_branch_call(
    ctx: &mut Ctx,
    block: &ast::Block,
    join_call: Option<&core::FuncCall>,
    env: Env,
) -> Result<core::FuncCall> {
    let mut statements = block.statements.clone();
    if let Some(join_call) = join_call {
        statements.push(join_statement(join_call)?);
    }
    emit_statements_call(ctx, statements, env)
}

fn join_statement(call: &core::FuncCall) -> Result<Stmt> {
    Ok(Stmt::Call {
        name: call.name.clone(),
        args: call.args.iter().map(join_arg).collect::<Result<Vec<_>>>()?,
    })
}

fn join_arg(expr: &core::Expr) -> Result<Expr> {
    match expr {
        core::Expr::Var(var) => Ok(Expr::Var(var.clone())),
        _ => bail!("if join arguments must be variables"),
    }
}

fn emit_statements_call(ctx: &mut Ctx, statements: Vec<Stmt>, env: Env) -> Result<core::FuncCall> {
    if statements.is_empty() {
        return Ok(terminal_unit_call(ctx, &env));
    }

    let liveness = Liveness::new(&statements);
    let name = ctx.fresh_label();
    let args = env
        .params_for(liveness.live_before(0))
        .into_iter()
        .map(|(var, _)| core::Expr::Var(var))
        .collect();
    emit_sequence(ctx, name.clone(), &statements, 0, env, &liveness)?;
    Ok(core::FuncCall { name, args })
}

fn continuation_call(
    ctx: &mut Ctx,
    statements: &[Stmt],
    index: usize,
    env: Env,
    liveness: &Liveness,
    overrides: &[(VarName, core::Expr)],
) -> Result<core::FuncCall> {
    if index + 1 == statements.len() {
        return Ok(terminal_unit_call(ctx, &env));
    }

    let next_index = index + 1;
    let next_name = ctx.fresh_label();
    let args = env
        .params_for(liveness.live_before(next_index))
        .into_iter()
        .map(|(var, _)| {
            overrides
                .iter()
                .find_map(|(name, expr)| (name == &var).then_some(expr.clone()))
                .unwrap_or(core::Expr::Var(var))
        })
        .collect();
    emit_sequence(
        ctx,
        next_name.clone(),
        statements,
        next_index,
        env,
        liveness,
    )?;
    Ok(core::FuncCall {
        name: next_name,
        args,
    })
}

fn unit_call() -> core::FuncCall {
    core::FuncCall {
        name: UNIT_FUNC.to_string(),
        args: vec![],
    }
}

fn terminal_unit_call(ctx: &mut Ctx, env: &Env) -> core::FuncCall {
    let params = env.linear_params();
    if params.is_empty() {
        return unit_call();
    }

    let name = ctx.fresh_label();
    ctx.insert_function(core::Function {
        name: name.clone(),
        params: params.clone(),
        body: core::Statement::Unit,
    });
    core::FuncCall {
        name,
        args: params
            .into_iter()
            .map(|(var, _)| core::Expr::Var(var))
            .collect(),
    }
}

fn fail_call() -> core::FuncCall {
    core::FuncCall {
        name: FAIL_FUNC.to_string(),
        args: vec![],
    }
}

fn terminal_fail_call(ctx: &mut Ctx, env: &Env) -> core::FuncCall {
    let params = env.linear_params();
    if params.is_empty() {
        return fail_call();
    }

    let name = ctx.fresh_label();
    ctx.insert_function(core::Function {
        name: name.clone(),
        params: params.clone(),
        body: core::Statement::Fail,
    });
    core::FuncCall {
        name,
        args: params
            .into_iter()
            .map(|(var, _)| core::Expr::Var(var))
            .collect(),
    }
}

fn value_expr(stmt: &Stmt) -> Result<&Expr> {
    match stmt {
        Stmt::Let { value, .. } => Ok(value),
        _ => bail!("statement has no value expression"),
    }
}

fn expect_var(expr: &Expr) -> Result<&VarName> {
    match expr {
        Expr::Var(var) => Ok(var),
        _ => bail!("expected variable"),
    }
}

fn ensure_type(env: &Env, var: &str, expected: &core::Type) -> Result<()> {
    match env.get(var) {
        Some(actual) if actual == expected => Ok(()),
        Some(actual) => bail!("expected variable {var} to have type {expected:?}, got {actual:?}"),
        None => bail!("undefined variable {var}"),
    }
}

fn ensure_type_matches(expected: &core::Type, actual: &core::Type) -> Result<()> {
    if expected == actual {
        Ok(())
    } else {
        bail!("expected type {expected:?}, got {actual:?}")
    }
}

fn ensure_sender_type<'a>(env: &'a Env, var: &str) -> Result<&'a core::Type> {
    match env.get(var) {
        Some(ty @ core::Type::Sender(_)) => Ok(ty),
        Some(ty) => bail!("expected variable {var} to be a sender, got {ty:?}"),
        None => bail!("undefined variable {var}"),
    }
}

fn ensure_sender_payload<'a>(env: &'a Env, var: &str) -> Result<&'a core::Type> {
    match env.get(var) {
        Some(core::Type::Sender(payload)) => Ok(payload),
        Some(ty) => bail!("expected variable {var} to be a sender, got {ty:?}"),
        None => bail!("undefined variable {var}"),
    }
}

fn ensure_receiver_payload<'a>(env: &'a Env, var: &str) -> Result<&'a core::Type> {
    match env.get(var) {
        Some(core::Type::Receiver(payload)) => Ok(payload),
        Some(ty) => bail!("expected variable {var} to be a receiver, got {ty:?}"),
        None => bail!("undefined variable {var}"),
    }
}

fn ensure_linear<'a>(env: &'a Env, var: &str) -> Result<&'a core::Type> {
    match env.get(var) {
        Some(ty) if ty.is_linear() => Ok(ty),
        Some(ty) => bail!("expected variable {var} to be linear, got {ty:?}"),
        None => bail!("undefined variable {var}"),
    }
}

fn infer_expr_type(expr: &Expr, env: &Env, ctx: &Ctx) -> Result<core::Type> {
    match expr {
        Expr::Int(_) => Ok(core::Type::Int),
        Expr::Var(var) => Ok(env.get(var).cloned().unwrap_or(core::Type::Int)),
        Expr::Ctor {
            type_name,
            variant,
            args,
        } => {
            let variant_def = find_variant(ctx, type_name, variant)?;
            if args.len() != variant_def.fields.len() {
                bail!(
                    "variant '{}::{}' expects {} fields, got {}",
                    type_name,
                    variant,
                    variant_def.fields.len(),
                    args.len()
                );
            }
            for (arg, expected_ty) in args.iter().zip(&variant_def.fields) {
                let actual_ty = infer_expr_type(arg, env, ctx)?;
                ensure_type_matches(expected_ty, &actual_ty)?;
            }
            Ok(core::Type::Adt(type_name.clone()))
        }
        Expr::BinaryOp { .. } => Ok(core::Type::Int),
        Expr::MethodCall { .. } => bail!("cannot infer this expression type yet"),
    }
}

fn find_adt<'a>(ctx: &'a Ctx, name: &str) -> Result<&'a core::AdtDef> {
    ctx.adts
        .iter()
        .find(|adt| adt.name == name)
        .ok_or_else(|| anyhow::anyhow!("unknown ADT type '{name}'"))
}

fn find_variant<'a>(ctx: &'a Ctx, type_name: &str, variant: &str) -> Result<&'a core::VariantDef> {
    let adt = find_adt(ctx, type_name)?;
    adt.variants
        .iter()
        .find(|variant_def| variant_def.name == variant)
        .ok_or_else(|| anyhow::anyhow!("unknown variant '{}::{}'", type_name, variant))
}

fn remove_linear_free_vars(target_env: &mut Env, expr: &Expr, source_env: &Env) {
    for var in expr.free_vars() {
        if source_env
            .get(&var)
            .map(core::Type::is_linear)
            .unwrap_or(false)
        {
            target_env.remove(&var);
        }
    }
}

fn lower_assignment_expr(target: &str, op: AssignOp, value: &Expr) -> Result<core::Expr> {
    let value = lower_expr(value)?;
    Ok(match op {
        AssignOp::Assign => value,
        AssignOp::AddAssign => core::Expr::Op(
            Box::new(core::Expr::Var(target.to_string())),
            core::OpKind::Add,
            Box::new(value),
        ),
        AssignOp::SubAssign => core::Expr::Op(
            Box::new(core::Expr::Var(target.to_string())),
            core::OpKind::Sub,
            Box::new(value),
        ),
        AssignOp::MulAssign => core::Expr::Op(
            Box::new(core::Expr::Var(target.to_string())),
            core::OpKind::Mul,
            Box::new(value),
        ),
    })
}

fn lower_expr(expr: &Expr) -> Result<core::Expr> {
    Ok(match expr {
        Expr::Int(n) => core::Expr::Num(*n),
        Expr::Var(var) => core::Expr::Var(var.clone()),
        Expr::Ctor {
            type_name,
            variant,
            args,
        } => core::Expr::Ctor {
            type_name: type_name.clone(),
            variant: variant.clone(),
            args: args.iter().map(lower_expr).collect::<Result<Vec<_>>>()?,
        },
        Expr::BinaryOp { lhs, op, rhs } => core::Expr::Op(
            Box::new(lower_expr(lhs)?),
            lower_binary_op(*op),
            Box::new(lower_expr(rhs)?),
        ),
        Expr::MethodCall { .. } => bail!("method calls cannot be used as core expressions"),
    })
}

fn lower_binary_op(op: BinaryOp) -> core::OpKind {
    match op {
        BinaryOp::Add => core::OpKind::Add,
        BinaryOp::Sub => core::OpKind::Sub,
        BinaryOp::Mul => core::OpKind::Mul,
        BinaryOp::Eq => core::OpKind::Eq,
        BinaryOp::Ne => core::OpKind::Ne,
        BinaryOp::Lt => core::OpKind::Lt,
        BinaryOp::Le => core::OpKind::Le,
        BinaryOp::Gt => core::OpKind::Gt,
        BinaryOp::Ge => core::OpKind::Ge,
    }
}

#[derive(Debug)]
struct Liveness {
    before: Vec<BTreeSet<VarName>>,
}

impl Liveness {
    fn new(statements: &[Stmt]) -> Self {
        let mut before = vec![BTreeSet::new(); statements.len()];
        let mut live = BTreeSet::new();

        for (index, stmt) in statements.iter().enumerate().rev() {
            for def in defined_vars(stmt) {
                live.remove(&def);
            }
            live.extend(used_vars(stmt));
            before[index] = live.clone();
        }

        Self { before }
    }

    fn live_before(&self, index: usize) -> &BTreeSet<VarName> {
        self.before.get(index).unwrap_or(&EMPTY_LIVE)
    }
}

static EMPTY_LIVE: BTreeSet<VarName> = BTreeSet::new();

fn used_vars(stmt: &Stmt) -> BTreeSet<VarName> {
    match stmt {
        Stmt::Let { value, .. } => value.free_vars(),
        Stmt::LetChannel { .. } => BTreeSet::new(),
        Stmt::Assign { target, op, value } => {
            let mut vars = value.free_vars();
            if !matches!(op, AssignOp::Assign) {
                vars.insert(target.clone());
            }
            vars
        }
        Stmt::Expr(expr) | Stmt::Assert(expr) => expr.free_vars(),
        Stmt::Call { args, .. } => args.iter().flat_map(Expr::free_vars).collect(),
        Stmt::Spawn(block) => block_free_vars(block),
        Stmt::While { cond, body } => {
            let mut vars = cond.free_vars();
            vars.extend(block_free_vars(body));
            vars
        }
        Stmt::If {
            cond,
            then_block,
            else_block,
        } => {
            let mut vars = cond.free_vars();
            vars.extend(block_free_vars(then_block));
            if let Some(else_block) = else_block {
                vars.extend(block_free_vars(else_block));
            }
            vars
        }
        Stmt::Match { scrutinee, arms } => {
            let mut vars = BTreeSet::from([scrutinee.clone()]);
            for arm in arms {
                let mut arm_vars = block_free_vars(&arm.block);
                for var in &arm.vars {
                    arm_vars.remove(var);
                }
                vars.extend(arm_vars);
            }
            vars
        }
    }
}

fn defined_vars(stmt: &Stmt) -> BTreeSet<VarName> {
    match stmt {
        Stmt::Let { binding, .. } => [binding.var.clone()].into(),
        Stmt::LetChannel {
            sender, receiver, ..
        } => [sender.clone(), receiver.clone()].into(),
        Stmt::Assign { target, .. } => [target.clone()].into(),
        Stmt::Expr(_)
        | Stmt::Call { .. }
        | Stmt::Spawn(_)
        | Stmt::While { .. }
        | Stmt::If { .. }
        | Stmt::Match { .. }
        | Stmt::Assert(_) => BTreeSet::new(),
    }
}

fn block_free_vars(block: &ast::Block) -> BTreeSet<VarName> {
    Liveness::new(&block.statements)
        .live_before(0)
        .iter()
        .cloned()
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::eval::Evaluator;
    use crate::sugar::ast::Binding;
    use crate::sugar::{check, parser};

    fn binding(name: &str) -> Binding {
        Binding {
            var: name.to_string(),
        }
    }

    fn var(name: &str) -> Expr {
        Expr::Var(name.to_string())
    }

    fn int(value: i32) -> Expr {
        Expr::Int(value)
    }

    fn core_var(name: &str) -> core::Expr {
        core::Expr::Var(name.to_string())
    }

    fn env(vars: &[(&str, core::Type)]) -> Env {
        let mut env = Env::new();
        for (name, ty) in vars {
            env.insert((*name).to_string(), ty.clone());
        }
        env
    }

    fn box_adt() -> core::AdtDef {
        core::AdtDef {
            name: "Box".to_string(),
            variants: vec![core::VariantDef {
                name: "Hold".to_string(),
                fields: vec![core::Type::int_sender()],
            }],
        }
    }

    fn convert_first_stmt(statements: Vec<Stmt>, env: Env) -> (core::Statement, Ctx) {
        convert_first_stmt_with_adts(statements, env, vec![])
    }

    fn convert_first_stmt_with_adts(
        statements: Vec<Stmt>,
        env: Env,
        adts: Vec<core::AdtDef>,
    ) -> (core::Statement, Ctx) {
        let liveness = Liveness::new(&statements);
        let mut ctx = Ctx::with_adts(adts);
        let stmt = desugar_stmt(&mut ctx, &statements, 0, env, &liveness)
            .expect("statement desugaring should succeed");
        (stmt, ctx)
    }

    fn generated_function<'a>(ctx: &'a Ctx, name: &str) -> &'a core::Function {
        ctx.functions
            .get(name)
            .expect("generated continuation should exist")
    }

    fn assert_call(call: &core::FuncCall, args: Vec<core::Expr>) {
        assert_eq!(call.args, args);
    }

    #[test]
    fn let_channel_statement_becomes_new() {
        let (stmt, ctx) = convert_first_stmt(
            vec![Stmt::LetChannel {
                payload: core::Type::Int,
                sender: "s".to_string(),
                receiver: "r".to_string(),
            }],
            Env::new(),
        );

        assert_eq!(
            stmt,
            core::Statement::New {
                payload: core::Type::Int,
                sender: "s".to_string(),
                receiver: "r".to_string(),
                body: core::FuncCall {
                    name: "__sugar_0".to_string(),
                    args: vec![core_var("s"), core_var("r")],
                },
            }
        );
        let unit_function = generated_function(&ctx, "__sugar_0");
        assert_eq!(
            unit_function.params,
            vec![
                ("s".to_string(), core::Type::int_sender()),
                ("r".to_string(), core::Type::int_receiver()),
            ]
        );
        assert_eq!(unit_function.body, core::Statement::Unit);
    }

    #[test]
    fn typed_channel_payload_program_runs_after_desugaring() {
        let sugar_program = parser::parse_program(
            r#"
            let s, r = channel<Sender<int>>();
            let inner_s, inner_r = channel();
            s.send(inner_s);
            let received_s = r.recv();
            received_s.send(1);
            let x = inner_r.recv();
            assert!(x == 1);
            "#,
        )
        .expect("sugar program should parse");
        check::check_program(&sugar_program).expect("sugar program should type check");
        let core_program = desugar_program(&sugar_program).expect("sugar program should desugar");
        let mut evaluator = Evaluator::new(core_program).expect("evaluator should initialize");

        for _ in 0..100 {
            if evaluator.is_done() {
                return;
            }
            evaluator.step().expect("evaluation should not fail");
        }

        panic!("evaluation did not finish");
    }

    #[test]
    fn adt_equality_assertion_runs_after_desugaring() {
        let sugar_program = parser::parse_program(
            r#"
            data Option = Some(int) | None
            let s, r = channel<Option>();
            s.send(Option::Some(42));
            let x = r.recv();
            assert!(x == Option::Some(42));
            "#,
        )
        .expect("ADT equality program should parse");
        check::check_program(&sugar_program).expect("sugar program should type check");
        let core_program = desugar_program(&sugar_program).expect("sugar program should desugar");
        let mut evaluator = Evaluator::new(core_program).expect("evaluator should initialize");

        for _ in 0..100 {
            if evaluator.is_done() {
                return;
            }
            evaluator.step().expect("evaluation should not fail");
        }

        panic!("evaluation did not finish");
    }

    #[test]
    fn typed_let_channel_statement_becomes_typed_new() {
        let payload = core::Type::int_sender();
        let (stmt, ctx) = convert_first_stmt(
            vec![Stmt::LetChannel {
                payload: payload.clone(),
                sender: "s".to_string(),
                receiver: "r".to_string(),
            }],
            Env::new(),
        );

        assert_eq!(
            stmt,
            core::Statement::New {
                payload: payload.clone(),
                sender: "s".to_string(),
                receiver: "r".to_string(),
                body: core::FuncCall {
                    name: "__sugar_0".to_string(),
                    args: vec![core_var("s"), core_var("r")],
                },
            }
        );
        let unit_function = generated_function(&ctx, "__sugar_0");
        assert_eq!(
            unit_function.params,
            vec![
                ("s".to_string(), core::Type::sender(payload.clone())),
                ("r".to_string(), core::Type::receiver(payload)),
            ]
        );
    }

    #[test]
    fn let_integer_statement_passes_value_to_continuation() {
        let (stmt, ctx) = convert_first_stmt(
            vec![
                Stmt::Let {
                    binding: binding("x"),
                    value: int(1),
                },
                Stmt::Assert(var("x")),
            ],
            Env::new(),
        );

        let call = match stmt {
            core::Statement::Call(call) => call,
            other => panic!("expected let to become continuation call, got {other:?}"),
        };
        assert_call(&call, vec![core::Expr::Num(1)]);

        let continuation = generated_function(&ctx, &call.name);
        assert_eq!(
            continuation.params,
            vec![("x".to_string(), core::Type::Int)]
        );
    }

    #[test]
    fn let_recv_statement_becomes_recv() {
        let (stmt, _) = convert_first_stmt(
            vec![
                Stmt::Let {
                    binding: binding("v"),
                    value: Expr::MethodCall {
                        receiver: Box::new(var("r")),
                        method: MethodCall::Recv,
                    },
                },
                Stmt::Assert(var("v")),
            ],
            env(&[("r", core::Type::int_receiver())]),
        );

        match stmt {
            core::Statement::Recv {
                receiver,
                var,
                body,
            } => {
                assert_eq!(receiver, "r");
                assert_eq!(var, "v");
                assert_call(&body, vec![core_var("r"), core_var("v")]);
            }
            other => panic!("expected recv statement, got {other:?}"),
        }
    }

    #[test]
    fn let_clone_statement_becomes_dup() {
        let (stmt, _) = convert_first_stmt(
            vec![
                Stmt::Let {
                    binding: binding("s2"),
                    value: Expr::MethodCall {
                        receiver: Box::new(var("s1")),
                        method: MethodCall::Clone,
                    },
                },
                Stmt::Expr(Expr::MethodCall {
                    receiver: Box::new(var("s2")),
                    method: MethodCall::Drop,
                }),
            ],
            env(&[("s1", core::Type::int_sender())]),
        );

        match stmt {
            core::Statement::Dup { sender, var, body } => {
                assert_eq!(sender, "s1");
                assert_eq!(var, "s2");
                assert_call(&body, vec![core_var("s1"), core_var("s2")]);
            }
            other => panic!("expected dup statement, got {other:?}"),
        }
    }

    #[test]
    fn assign_statement_passes_updated_value_to_continuation() {
        let (stmt, _) = convert_first_stmt(
            vec![
                Stmt::Assign {
                    target: "sum".to_string(),
                    op: AssignOp::AddAssign,
                    value: int(1),
                },
                Stmt::Assert(var("sum")),
            ],
            env(&[("sum", core::Type::Int)]),
        );

        let call = match stmt {
            core::Statement::Call(call) => call,
            other => panic!("expected assignment to become continuation call, got {other:?}"),
        };
        assert_call(
            &call,
            vec![core::Expr::Op(
                Box::new(core_var("sum")),
                core::OpKind::Add,
                Box::new(core::Expr::Num(1)),
            )],
        );
    }

    #[test]
    fn send_statement_becomes_send() {
        let (stmt, _) = convert_first_stmt(
            vec![
                Stmt::Expr(Expr::MethodCall {
                    receiver: Box::new(var("s")),
                    method: MethodCall::Send(Box::new(int(1))),
                }),
                Stmt::Expr(Expr::MethodCall {
                    receiver: Box::new(var("s")),
                    method: MethodCall::Drop,
                }),
            ],
            env(&[("s", core::Type::int_sender())]),
        );

        match stmt {
            core::Statement::Send {
                sender,
                value,
                body,
            } => {
                assert_eq!(sender, "s");
                assert_eq!(value, core::Expr::Num(1));
                assert_call(&body, vec![core_var("s")]);
            }
            other => panic!("expected send statement, got {other:?}"),
        }
    }

    #[test]
    fn send_statement_moves_linear_payload() {
        let (stmt, ctx) = convert_first_stmt(
            vec![Stmt::Expr(Expr::MethodCall {
                receiver: Box::new(var("s")),
                method: MethodCall::Send(Box::new(var("inner_s"))),
            })],
            env(&[
                ("s", core::Type::sender(core::Type::int_sender())),
                ("inner_s", core::Type::int_sender()),
            ]),
        );

        match stmt {
            core::Statement::Send {
                sender,
                value,
                body,
            } => {
                assert_eq!(sender, "s");
                assert_eq!(value, core_var("inner_s"));
                assert_call(&body, vec![core_var("s")]);
                let unit_function = generated_function(&ctx, &body.name);
                assert_eq!(
                    unit_function.params,
                    vec![(
                        "s".to_string(),
                        core::Type::sender(core::Type::int_sender())
                    )]
                );
            }
            other => panic!("expected send statement, got {other:?}"),
        }
    }

    #[test]
    fn let_adt_constructor_moves_linear_fields_to_the_constructed_value() {
        let (stmt, ctx) = convert_first_stmt_with_adts(
            vec![
                Stmt::Let {
                    binding: binding("b"),
                    value: Expr::Ctor {
                        type_name: "Box".to_string(),
                        variant: "Hold".to_string(),
                        args: vec![var("s")],
                    },
                },
                Stmt::Expr(Expr::MethodCall {
                    receiver: Box::new(var("b")),
                    method: MethodCall::Drop,
                }),
            ],
            env(&[("s", core::Type::int_sender())]),
            vec![box_adt()],
        );

        let call = match stmt {
            core::Statement::Call(call) => call,
            other => panic!("expected constructor let to become continuation call, got {other:?}"),
        };
        assert_call(
            &call,
            vec![core::Expr::Ctor {
                type_name: "Box".to_string(),
                variant: "Hold".to_string(),
                args: vec![core_var("s")],
            }],
        );

        let continuation = generated_function(&ctx, &call.name);
        assert_eq!(
            continuation.params,
            vec![("b".to_string(), core::Type::Adt("Box".to_string()))]
        );
    }

    #[test]
    fn drop_statement_spawns_unit_function_for_dropped_variable_and_continues() {
        let (stmt, ctx) = convert_first_stmt(
            vec![
                Stmt::Expr(Expr::MethodCall {
                    receiver: Box::new(var("s")),
                    method: MethodCall::Drop,
                }),
                Stmt::Assert(int(1)),
            ],
            env(&[("s", core::Type::int_sender())]),
        );

        let (drop_call, continuation) = match stmt {
            core::Statement::Spawn(drop_call, continuation) => (drop_call, continuation),
            other => panic!("expected drop to become spawn statement, got {other:?}"),
        };
        assert_call(&drop_call, vec![core_var("s")]);
        assert_call(&continuation, vec![]);

        let drop_function = generated_function(&ctx, &drop_call.name);
        assert_eq!(
            drop_function.params,
            vec![("s".to_string(), core::Type::int_sender())]
        );
        assert_eq!(drop_function.body, core::Statement::Unit);
    }

    #[test]
    fn function_call_statement_becomes_core_call() {
        let (stmt, _) = convert_first_stmt(
            vec![Stmt::Call {
                name: "f".to_string(),
                args: vec![int(1), var("x")],
            }],
            env(&[("x", core::Type::Int)]),
        );

        assert_eq!(
            stmt,
            core::Statement::Call(core::FuncCall {
                name: "f".to_string(),
                args: vec![core::Expr::Num(1), core_var("x")],
            })
        );
    }

    #[test]
    fn assert_statement_runs_continuation_on_success() {
        let (stmt, ctx) = convert_first_stmt(
            vec![
                Stmt::Assert(Expr::BinaryOp {
                    lhs: Box::new(var("x")),
                    op: BinaryOp::Eq,
                    rhs: Box::new(int(1)),
                }),
                Stmt::Call {
                    name: "next".to_string(),
                    args: vec![var("x")],
                },
            ],
            env(&[("x", core::Type::Int), ("s", core::Type::int_sender())]),
        );

        let then_call = match stmt {
            core::Statement::If(cond, then_call, else_call) => {
                assert_eq!(
                    cond,
                    core::Expr::Op(
                        Box::new(core_var("x")),
                        core::OpKind::Eq,
                        Box::new(core::Expr::Num(1)),
                    )
                );
                assert_call(&then_call, vec![core_var("x"), core_var("s")]);
                assert_call(&else_call, vec![core_var("s")]);
                then_call
            }
            other => panic!("expected assert to become if statement, got {other:?}"),
        };

        let continuation = generated_function(&ctx, &then_call.name);
        assert_eq!(
            continuation.body,
            core::Statement::Call(core::FuncCall {
                name: "next".to_string(),
                args: vec![core_var("x")],
            })
        );

        let failure = generated_function(&ctx, "__sugar_1");
        assert_eq!(
            failure.params,
            vec![("s".to_string(), core::Type::int_sender())]
        );
        assert_eq!(failure.body, core::Statement::Fail);
    }

    #[test]
    fn final_assert_statement_succeeds_to_unit_with_live_linear_variables() {
        let (stmt, ctx) = convert_first_stmt(
            vec![Stmt::Assert(Expr::BinaryOp {
                lhs: Box::new(var("x")),
                op: BinaryOp::Eq,
                rhs: Box::new(int(1)),
            })],
            env(&[
                ("x", core::Type::Int),
                ("s", core::Type::int_sender()),
                ("r", core::Type::int_receiver()),
            ]),
        );

        match stmt {
            core::Statement::If(cond, then_call, else_call) => {
                assert_eq!(
                    cond,
                    core::Expr::Op(
                        Box::new(core_var("x")),
                        core::OpKind::Eq,
                        Box::new(core::Expr::Num(1)),
                    )
                );
                assert_eq!(then_call.name, "__sugar_0");
                assert_eq!(then_call.args, vec![core_var("s"), core_var("r")]);
                assert_eq!(else_call.name, "__sugar_1");
                assert_eq!(else_call.args, vec![core_var("s"), core_var("r")]);
            }
            other => panic!("expected assert to become if statement, got {other:?}"),
        }
        let unit_function = generated_function(&ctx, "__sugar_0");
        assert_eq!(
            unit_function.params,
            vec![
                ("s".to_string(), core::Type::int_sender()),
                ("r".to_string(), core::Type::int_receiver()),
            ]
        );
        assert_eq!(unit_function.body, core::Statement::Unit);
        let fail_function = generated_function(&ctx, "__sugar_1");
        assert_eq!(
            fail_function.params,
            vec![
                ("s".to_string(), core::Type::int_sender()),
                ("r".to_string(), core::Type::int_receiver()),
            ]
        );
        assert_eq!(fail_function.body, core::Statement::Fail);
    }

    #[test]
    fn spawn_statement_becomes_spawn() {
        let (stmt, ctx) = convert_first_stmt(
            vec![
                Stmt::Spawn(ast::Block {
                    statements: vec![Stmt::Expr(Expr::MethodCall {
                        receiver: Box::new(var("s")),
                        method: MethodCall::Send(Box::new(int(1))),
                    })],
                }),
                Stmt::Let {
                    binding: binding("v"),
                    value: Expr::MethodCall {
                        receiver: Box::new(var("r")),
                        method: MethodCall::Recv,
                    },
                },
            ],
            env(&[
                ("s", core::Type::int_sender()),
                ("r", core::Type::int_receiver()),
            ]),
        );

        let (spawned, continuation) = match stmt {
            core::Statement::Spawn(spawned, continuation) => (spawned, continuation),
            other => panic!("expected spawn statement, got {other:?}"),
        };
        assert_call(&spawned, vec![core_var("s")]);
        assert_call(&continuation, vec![core_var("r")]);

        let spawned_function = generated_function(&ctx, &spawned.name);
        assert_eq!(
            spawned_function.params,
            vec![("s".to_string(), core::Type::int_sender())]
        );

        let continuation_function = generated_function(&ctx, &continuation.name);
        assert_eq!(
            continuation_function.params,
            vec![("r".to_string(), core::Type::int_receiver())]
        );
    }

    #[test]
    fn if_statement_becomes_core_if() {
        let (stmt, ctx) = convert_first_stmt(
            vec![Stmt::If {
                cond: var("x"),
                then_block: ast::Block {
                    statements: vec![Stmt::Assert(int(1))],
                },
                else_block: Some(ast::Block {
                    statements: vec![Stmt::Assert(int(0))],
                }),
            }],
            env(&[("x", core::Type::Int)]),
        );

        let (then_call, else_call) = match stmt {
            core::Statement::If(cond, then_call, else_call) => {
                assert_eq!(cond, core_var("x"));
                (then_call, else_call)
            }
            other => panic!("expected if statement, got {other:?}"),
        };
        assert_call(&then_call, vec![]);
        assert_call(&else_call, vec![]);

        let then_function = generated_function(&ctx, &then_call.name);
        assert!(matches!(then_function.body, core::Statement::If(_, _, _)));

        let else_function = generated_function(&ctx, &else_call.name);
        assert!(matches!(else_function.body, core::Statement::If(_, _, _)));
    }

    #[test]
    fn if_statement_shares_continuation_after_branches() {
        let (stmt, ctx) = convert_first_stmt(
            vec![
                Stmt::If {
                    cond: var("x"),
                    then_block: ast::Block { statements: vec![] },
                    else_block: Some(ast::Block { statements: vec![] }),
                },
                Stmt::Assert(var("y")),
            ],
            env(&[("x", core::Type::Int), ("y", core::Type::Int)]),
        );

        let (then_call, else_call) = match stmt {
            core::Statement::If(cond, then_call, else_call) => {
                assert_eq!(cond, core_var("x"));
                (then_call, else_call)
            }
            other => panic!("expected if statement, got {other:?}"),
        };
        assert_call(&then_call, vec![core_var("y")]);
        assert_call(&else_call, vec![core_var("y")]);

        let then_function = generated_function(&ctx, &then_call.name);
        let else_function = generated_function(&ctx, &else_call.name);
        let then_join = match &then_function.body {
            core::Statement::Call(call) => call,
            other => panic!("expected then branch to call join, got {other:?}"),
        };
        let else_join = match &else_function.body {
            core::Statement::Call(call) => call,
            other => panic!("expected else branch to call join, got {other:?}"),
        };
        assert_eq!(then_join.name, else_join.name);
        assert_call(then_join, vec![core_var("y")]);
        assert_call(else_join, vec![core_var("y")]);

        let join_function = generated_function(&ctx, &then_join.name);
        assert_eq!(
            join_function.params,
            vec![("y".to_string(), core::Type::Int)]
        );
        assert!(matches!(join_function.body, core::Statement::If(_, _, _)));
    }

    #[test]
    fn match_statement_becomes_core_match() {
        let (stmt, ctx) = convert_first_stmt_with_adts(
            vec![Stmt::Match {
                scrutinee: "b".to_string(),
                arms: vec![ast::MatchArm {
                    type_name: "Box".to_string(),
                    variant: "Hold".to_string(),
                    vars: vec!["s".to_string()],
                    block: ast::Block {
                        statements: vec![Stmt::Expr(Expr::MethodCall {
                            receiver: Box::new(var("s")),
                            method: MethodCall::Drop,
                        })],
                    },
                }],
            }],
            env(&[("b", core::Type::Adt("Box".to_string()))]),
            vec![box_adt()],
        );

        let arms = match stmt {
            core::Statement::Match { scrutinee, arms } => {
                assert_eq!(scrutinee, "b");
                arms
            }
            other => panic!("expected core match statement, got {other:?}"),
        };
        assert_eq!(arms.len(), 1);
        assert_eq!(arms[0].type_name, "Box");
        assert_eq!(arms[0].variant, "Hold");
        assert_eq!(arms[0].vars, vec!["s".to_string()]);

        let arm_function = generated_function(&ctx, &arms[0].body.name);
        assert_eq!(
            arm_function.params,
            vec![("s".to_string(), core::Type::int_sender())]
        );
    }

    #[test]
    fn while_statement_becomes_loop_call() {
        let (stmt, ctx) = convert_first_stmt(
            vec![
                Stmt::While {
                    cond: Expr::BinaryOp {
                        lhs: Box::new(var("sum")),
                        op: BinaryOp::Lt,
                        rhs: Box::new(int(2)),
                    },
                    body: ast::Block {
                        statements: vec![Stmt::Assign {
                            target: "sum".to_string(),
                            op: AssignOp::AddAssign,
                            value: int(1),
                        }],
                    },
                },
                Stmt::Assert(var("sum")),
            ],
            env(&[("sum", core::Type::Int)]),
        );

        let loop_call = match stmt {
            core::Statement::Call(call) => call,
            other => panic!("expected while to become loop call, got {other:?}"),
        };
        assert_call(&loop_call, vec![core_var("sum")]);

        let loop_function = generated_function(&ctx, &loop_call.name);
        assert_eq!(
            loop_function.params,
            vec![("sum".to_string(), core::Type::Int)]
        );
        match &loop_function.body {
            core::Statement::If(cond, body_call, after_call) => {
                assert_eq!(
                    cond,
                    &core::Expr::Op(
                        Box::new(core_var("sum")),
                        core::OpKind::Lt,
                        Box::new(core::Expr::Num(2)),
                    )
                );
                assert_call(body_call, vec![core_var("sum")]);
                assert_call(after_call, vec![core_var("sum")]);
            }
            other => panic!("expected loop function body to be if, got {other:?}"),
        }
    }

    #[test]
    fn undefined_variables_become_core_init_arguments() {
        let program = ast::Program {
            adts: vec![],
            statements: vec![Stmt::Assert(var("x"))],
        };

        let core = desugar_program(&program).expect("program desugaring should succeed");

        assert_eq!(
            core.init,
            core::FuncCall {
                name: ENTRY_FUNC.to_string(),
                args: vec![core_var("x")],
            }
        );
        let entry = core
            .functions
            .get(ENTRY_FUNC)
            .expect("entry function should exist");
        assert_eq!(entry.params, vec![("x".to_string(), core::Type::Int)]);
        match &entry.body {
            core::Statement::If(cond, then_call, else_call) => {
                assert_eq!(cond, &core_var("x"));
                assert_call(then_call, vec![]);
                assert_call(else_call, vec![]);
            }
            other => panic!("expected entry body to be assert if, got {other:?}"),
        }
    }

    #[test]
    fn assignment_defines_int_variable_without_core_init_argument() {
        let program = ast::Program {
            adts: vec![],
            statements: vec![
                Stmt::Assign {
                    target: "x".to_string(),
                    op: AssignOp::Assign,
                    value: int(1),
                },
                Stmt::Assert(var("x")),
            ],
        };

        let core = desugar_program(&program).expect("program desugaring should succeed");

        assert_eq!(
            core.init,
            core::FuncCall {
                name: ENTRY_FUNC.to_string(),
                args: vec![],
            }
        );
        let entry = core
            .functions
            .get(ENTRY_FUNC)
            .expect("entry function should exist");
        assert_eq!(entry.params, vec![]);
        match &entry.body {
            core::Statement::Call(call) => assert_call(call, vec![core::Expr::Num(1)]),
            other => panic!("expected assignment to become continuation call, got {other:?}"),
        }
    }
}

use std::collections::{BTreeSet, HashMap};

use crate::core::ast::{self as core, AdtDef, VariantDef};

use super::ast::{AssignOp, BinaryOp, Block, Expr, MatchArm, MethodCall, Program, Stmt};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Int,
    Adt(String),
    Sender(Box<Type>),
    Receiver(Box<Type>),
    Unit,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CheckError {
    UndefinedVariable { var: String },
    TypeMismatch { expected: Type, actual: Type },
    UseAfterConsume { var: String },
    InvalidAdt { message: String },
}

#[derive(Debug, Clone)]
struct BindingState {
    ty: Type,
    consumed: bool,
}

#[derive(Debug, Clone, Default)]
struct Env {
    vars: HashMap<String, BindingState>,
}

impl Env {
    fn declare(&mut self, var: impl Into<String>, ty: Type) {
        self.vars.insert(
            var.into(),
            BindingState {
                ty,
                consumed: false,
            },
        );
    }

    fn consume(&mut self, var: &str) -> Result<(), CheckError> {
        let binding = self.get_mut(var)?;
        binding.consumed = true;
        Ok(())
    }

    fn get(&self, var: &str) -> Result<&BindingState, CheckError> {
        let binding = self
            .vars
            .get(var)
            .ok_or_else(|| CheckError::UndefinedVariable {
                var: var.to_string(),
            })?;
        if binding.consumed {
            return Err(CheckError::UseAfterConsume {
                var: var.to_string(),
            });
        }
        Ok(binding)
    }

    fn ensure_int(&mut self, var: &str) -> Result<&BindingState, CheckError> {
        if !self.vars.contains_key(var) {
            self.declare(var.to_string(), Type::Int);
        }
        self.get(var)
    }

    fn get_mut(&mut self, var: &str) -> Result<&mut BindingState, CheckError> {
        let binding = self
            .vars
            .get_mut(var)
            .ok_or_else(|| CheckError::UndefinedVariable {
                var: var.to_string(),
            })?;
        if binding.consumed {
            return Err(CheckError::UseAfterConsume {
                var: var.to_string(),
            });
        }
        Ok(binding)
    }

    fn ty_of(&mut self, var: &str) -> Result<Type, CheckError> {
        Ok(self.ensure_int(var)?.ty.clone())
    }
}

pub fn check_program(program: &Program) -> Result<(), CheckError> {
    check_adts(&program.adts)?;
    let mut env = Env::default();
    check_stmts(&program.statements, &mut env, &program.adts)
}

fn check_stmts(stmts: &[Stmt], env: &mut Env, adts: &[AdtDef]) -> Result<(), CheckError> {
    for stmt in stmts {
        check_stmt(stmt, env, adts)?;
    }
    Ok(())
}

fn check_stmt(stmt: &Stmt, env: &mut Env, adts: &[AdtDef]) -> Result<(), CheckError> {
    match stmt {
        Stmt::Let { binding, value } => {
            let ty = check_expr(value, env, adts)?;
            if !matches!(
                value,
                Expr::MethodCall {
                    method: MethodCall::Recv | MethodCall::Clone,
                    ..
                }
            ) {
                consume_linear_vars_in_expr(value, env)?;
            }
            env.declare(binding.var.clone(), ty);
            Ok(())
        }
        Stmt::LetChannel {
            payload,
            sender,
            receiver,
        } => {
            let payload = Type::from_core(payload);
            env.declare(sender.clone(), Type::sender(payload.clone()));
            env.declare(receiver.clone(), Type::receiver(payload));
            Ok(())
        }
        Stmt::Assign { target, op, value } => {
            expect_var_type(env, target, Type::Int)?;
            let value_ty = check_expr(value, env, adts)?;
            expect_type(Type::Int, value_ty)?;
            if !matches!(op, AssignOp::Assign) {
                expect_var_type(env, target, Type::Int)?;
            }
            Ok(())
        }
        Stmt::Expr(expr) => {
            check_expr(expr, env, adts)?;
            Ok(())
        }
        Stmt::Call { args, .. } => {
            for arg in args {
                let ty = check_expr(arg, env, adts)?;
                expect_type(Type::Int, ty)?;
            }
            Ok(())
        }
        Stmt::Spawn(block) => {
            let mut child_env = env.clone();
            let moved_vars = block_external_vars(block)
                .into_iter()
                .filter(|var| {
                    env.vars
                        .get(var)
                        .map(|binding| binding.ty.is_linear())
                        .unwrap_or(false)
                })
                .collect::<Vec<_>>();
            check_block(block, &mut child_env, adts)?;
            for var in moved_vars {
                env.consume(&var)?;
            }
            Ok(())
        }
        Stmt::While { cond, body } => {
            let cond_ty = check_expr(cond, env, adts)?;
            expect_type(Type::Int, cond_ty)?;
            let mut body_env = env.clone();
            check_block(body, &mut body_env, adts)?;
            Ok(())
        }
        Stmt::If {
            cond,
            then_block,
            else_block,
        } => {
            let cond_ty = check_expr(cond, env, adts)?;
            expect_type(Type::Int, cond_ty)?;
            let mut then_env = env.clone();
            check_block(then_block, &mut then_env, adts)?;
            if let Some(else_block) = else_block {
                let mut else_env = env.clone();
                check_block(else_block, &mut else_env, adts)?;
            }
            Ok(())
        }
        Stmt::Match { scrutinee, arms } => check_match(scrutinee, arms, env, adts),
        Stmt::Assert(expr) => {
            check_assert_expr(expr, env, adts)?;
            consume_linear_vars_in_expr(expr, env)?;
            Ok(())
        }
    }
}

fn check_block(block: &Block, env: &mut Env, adts: &[AdtDef]) -> Result<(), CheckError> {
    check_stmts(&block.statements, env, adts)
}

fn check_expr(expr: &Expr, env: &mut Env, adts: &[AdtDef]) -> Result<Type, CheckError> {
    match expr {
        Expr::Int(_) => Ok(Type::Int),
        Expr::Var(var) => env.ty_of(var),
        Expr::Ctor {
            type_name,
            variant,
            args,
        } => {
            let variant_def = find_variant(adts, type_name, variant)?;
            if args.len() != variant_def.fields.len() {
                return Err(CheckError::InvalidAdt {
                    message: format!(
                        "variant '{}::{}' expects {} fields, got {}",
                        type_name,
                        variant,
                        variant_def.fields.len(),
                        args.len()
                    ),
                });
            }
            for (arg, expected) in args.iter().zip(&variant_def.fields) {
                let actual = check_expr(arg, env, adts)?;
                expect_type(Type::from_core(expected), actual)?;
            }
            ensure_linear_vars_consumed_once(args, env)?;
            Ok(Type::Adt(type_name.clone()))
        }
        Expr::MethodCall { receiver, method } => check_method_call(receiver, method, env, adts),
        Expr::BinaryOp { lhs, op, rhs } => {
            let lhs_ty = check_expr(lhs, env, adts)?;
            let rhs_ty = check_expr(rhs, env, adts)?;
            match op {
                BinaryOp::Eq | BinaryOp::Ne => {
                    expect_type(Type::Int, lhs_ty)?;
                    expect_type(Type::Int, rhs_ty)?;
                    Ok(Type::Int)
                }
                BinaryOp::Add
                | BinaryOp::Sub
                | BinaryOp::Mul
                | BinaryOp::Lt
                | BinaryOp::Le
                | BinaryOp::Gt
                | BinaryOp::Ge => {
                    expect_type(Type::Int, lhs_ty)?;
                    expect_type(Type::Int, rhs_ty)?;
                    Ok(Type::Int)
                }
            }
        }
    }
}

fn check_assert_expr(expr: &Expr, env: &mut Env, adts: &[AdtDef]) -> Result<(), CheckError> {
    if let Expr::BinaryOp { lhs, op, rhs } = expr {
        if matches!(op, BinaryOp::Eq | BinaryOp::Ne) {
            let lhs_ty = check_expr(lhs, env, adts)?;
            let rhs_ty = check_expr(rhs, env, adts)?;
            if lhs_ty == rhs_ty
                && matches!(lhs_ty, Type::Adt(_))
                && supports_adt_equality(lhs, rhs, adts)?
            {
                return Ok(());
            }
            expect_type(Type::Int, lhs_ty)?;
            expect_type(Type::Int, rhs_ty)?;
            return Ok(());
        }
    }

    let ty = check_expr(expr, env, adts)?;
    expect_type(Type::Int, ty)
}

fn supports_adt_equality(lhs: &Expr, rhs: &Expr, adts: &[AdtDef]) -> Result<bool, CheckError> {
    let ctor = match (lhs, rhs) {
        (Expr::Var(_), Expr::Ctor { .. }) => rhs,
        (Expr::Ctor { .. }, Expr::Var(_)) => lhs,
        _ => return Ok(false),
    };
    let Expr::Ctor {
        type_name,
        variant,
        args,
    } = ctor
    else {
        return Ok(false);
    };
    let variant_def = find_variant(adts, type_name, variant)?;
    if args.len() != variant_def.fields.len() {
        return Ok(false);
    }
    let adt = find_adt(adts, type_name)?;
    for variant_def in &adt.variants {
        for field_ty in &variant_def.fields {
            if field_ty != &core::Type::Int {
                return Err(CheckError::InvalidAdt {
                    message: format!(
                        "ADT equality is only supported when all fields are int, but '{}::{}' has field {:?}",
                        type_name, variant_def.name, field_ty
                    ),
                });
            }
        }
    }
    for arg in args {
        if !matches!(arg, Expr::Int(_) | Expr::Var(_) | Expr::BinaryOp { .. }) {
            return Err(CheckError::InvalidAdt {
                message: format!(
                    "ADT equality pattern for '{}::{}' must contain int expressions",
                    type_name, variant
                ),
            });
        }
    }
    Ok(true)
}

fn ensure_linear_vars_consumed_once(args: &[Expr], env: &Env) -> Result<(), CheckError> {
    let mut usage_env = env.clone();
    for arg in args {
        consume_linear_vars_in_expr_ordered(arg, &mut usage_env)?;
    }
    Ok(())
}

fn consume_linear_vars_in_expr_ordered(expr: &Expr, env: &mut Env) -> Result<(), CheckError> {
    match expr {
        Expr::Int(_) => Ok(()),
        Expr::Var(var) => {
            let should_consume = env
                .vars
                .get(var)
                .map(|binding| binding.ty.is_linear())
                .unwrap_or(false);
            if should_consume {
                env.consume(var)?;
            }
            Ok(())
        }
        Expr::Ctor { args, .. } => {
            for arg in args {
                consume_linear_vars_in_expr_ordered(arg, env)?;
            }
            Ok(())
        }
        Expr::MethodCall { receiver, method } => {
            match method {
                MethodCall::Send(value) => consume_linear_vars_in_expr_ordered(value, env)?,
                MethodCall::Drop => consume_linear_vars_in_expr_ordered(receiver, env)?,
                MethodCall::Recv | MethodCall::Clone => {}
            }
            Ok(())
        }
        Expr::BinaryOp { lhs, rhs, .. } => {
            consume_linear_vars_in_expr_ordered(lhs, env)?;
            consume_linear_vars_in_expr_ordered(rhs, env)
        }
    }
}

fn check_method_call(
    receiver: &Expr,
    method: &MethodCall,
    env: &mut Env,
    adts: &[AdtDef],
) -> Result<Type, CheckError> {
    let receiver_var = expect_receiver_var(receiver)?;
    match method {
        MethodCall::Send(value) => {
            let sender_ty = env.ty_of(receiver_var)?;
            let payload =
                sender_ty
                    .payload_for_sender()
                    .ok_or_else(|| CheckError::TypeMismatch {
                        expected: Type::int_sender(),
                        actual: sender_ty.clone(),
                    })?;
            let value_ty = check_expr(value, env, adts)?;
            expect_type(payload.clone(), value_ty)?;
            consume_linear_vars_in_expr(value, env)?;
            Ok(Type::Unit)
        }
        MethodCall::Recv => {
            let receiver_ty = env.ty_of(receiver_var)?;
            let payload =
                receiver_ty
                    .payload_for_receiver()
                    .ok_or_else(|| CheckError::TypeMismatch {
                        expected: Type::int_receiver(),
                        actual: receiver_ty.clone(),
                    })?;
            Ok(payload.clone())
        }
        MethodCall::Drop => {
            let ty = env.ty_of(receiver_var)?;
            if !ty.is_linear() {
                return Err(CheckError::TypeMismatch {
                    expected: Type::int_sender(),
                    actual: ty,
                });
            }
            env.consume(receiver_var)?;
            Ok(Type::Unit)
        }
        MethodCall::Clone => {
            let sender_ty = env.ty_of(receiver_var)?;
            if !matches!(sender_ty, Type::Sender(_)) {
                return Err(CheckError::TypeMismatch {
                    expected: Type::int_sender(),
                    actual: sender_ty,
                });
            }
            Ok(sender_ty)
        }
    }
}

fn check_match(
    scrutinee: &str,
    arms: &[MatchArm],
    env: &mut Env,
    adts: &[AdtDef],
) -> Result<(), CheckError> {
    let scrutinee_ty = env.ty_of(scrutinee)?;
    let Type::Adt(type_name) = scrutinee_ty else {
        return Err(CheckError::TypeMismatch {
            expected: Type::Adt("<adt>".to_string()),
            actual: scrutinee_ty,
        });
    };
    check_match_arms(arms, adts, &type_name)?;
    env.consume(scrutinee)?;
    let after_scrutinee_env = env.clone();
    let adt = find_adt(adts, &type_name)?;
    for arm in arms {
        let variant = adt
            .variants
            .iter()
            .find(|variant| variant.name == arm.variant)
            .expect("match arms were already checked");
        let mut arm_env = after_scrutinee_env.clone();
        for (var, field_ty) in arm.vars.iter().zip(&variant.fields) {
            arm_env.declare(var.clone(), Type::from_core(field_ty));
        }
        check_block(&arm.block, &mut arm_env, adts)?;
    }
    Ok(())
}

fn check_adts(adts: &[AdtDef]) -> Result<(), CheckError> {
    let mut names = BTreeSet::new();
    for adt in adts {
        if !names.insert(adt.name.clone()) {
            return Err(CheckError::InvalidAdt {
                message: format!("ADT '{}' is defined multiple times", adt.name),
            });
        }
        let mut variants = BTreeSet::new();
        for variant in &adt.variants {
            if !variants.insert(variant.name.clone()) {
                return Err(CheckError::InvalidAdt {
                    message: format!(
                        "variant '{}::{}' is defined multiple times",
                        adt.name, variant.name
                    ),
                });
            }
            for field in &variant.fields {
                check_core_type(field, adts)?;
            }
        }
    }
    Ok(())
}

fn check_core_type(ty: &core::Type, adts: &[AdtDef]) -> Result<(), CheckError> {
    match ty {
        core::Type::Int => Ok(()),
        core::Type::Adt(name) => {
            find_adt(adts, name)?;
            Ok(())
        }
        core::Type::Sender(payload) | core::Type::Receiver(payload) => {
            check_core_type(payload, adts)
        }
        core::Type::Func { params } => {
            for param in params {
                check_core_type(param, adts)?;
            }
            Ok(())
        }
    }
}

fn check_match_arms(
    arms: &[MatchArm],
    adts: &[AdtDef],
    expected_type: &str,
) -> Result<(), CheckError> {
    let adt = find_adt(adts, expected_type)?;
    let mut seen = BTreeSet::new();
    for arm in arms {
        if arm.type_name != expected_type {
            return Err(CheckError::InvalidAdt {
                message: format!(
                    "match arm uses ADT '{}', expected '{}'",
                    arm.type_name, expected_type
                ),
            });
        }
        let variant = find_variant(adts, &arm.type_name, &arm.variant)?;
        if !seen.insert(arm.variant.clone()) {
            return Err(CheckError::InvalidAdt {
                message: format!(
                    "match arm for '{}::{}' is defined multiple times",
                    arm.type_name, arm.variant
                ),
            });
        }
        if arm.vars.len() != variant.fields.len() {
            return Err(CheckError::InvalidAdt {
                message: format!(
                    "variant '{}::{}' expects {} fields, got {}",
                    arm.type_name,
                    arm.variant,
                    variant.fields.len(),
                    arm.vars.len()
                ),
            });
        }
    }
    for variant in &adt.variants {
        if !seen.contains(&variant.name) {
            return Err(CheckError::InvalidAdt {
                message: format!("match is missing arm '{}::{}'", adt.name, variant.name),
            });
        }
    }
    Ok(())
}

fn find_adt<'a>(adts: &'a [AdtDef], name: &str) -> Result<&'a AdtDef, CheckError> {
    adts.iter()
        .find(|adt| adt.name == name)
        .ok_or_else(|| CheckError::InvalidAdt {
            message: format!("unknown ADT type '{}'", name),
        })
}

fn find_variant<'a>(
    adts: &'a [AdtDef],
    type_name: &str,
    variant: &str,
) -> Result<&'a VariantDef, CheckError> {
    let adt = find_adt(adts, type_name)?;
    adt.variants
        .iter()
        .find(|variant_def| variant_def.name == variant)
        .ok_or_else(|| CheckError::InvalidAdt {
            message: format!("unknown variant '{}::{}'", type_name, variant),
        })
}

fn expect_receiver_var(expr: &Expr) -> Result<&str, CheckError> {
    match expr {
        Expr::Var(var) => Ok(var),
        _ => Err(CheckError::TypeMismatch {
            expected: Type::int_sender(),
            actual: Type::Int,
        }),
    }
}

fn expect_var_type(env: &mut Env, var: &str, expected: Type) -> Result<(), CheckError> {
    let actual = env.ty_of(var)?;
    expect_type(expected, actual)
}

fn expect_type(expected: Type, actual: Type) -> Result<(), CheckError> {
    if expected == actual {
        Ok(())
    } else {
        Err(CheckError::TypeMismatch { expected, actual })
    }
}

fn consume_linear_vars_in_expr(expr: &Expr, env: &mut Env) -> Result<(), CheckError> {
    for var in expr.free_vars() {
        let should_consume = env
            .vars
            .get(&var)
            .map(|binding| binding.ty.is_linear())
            .unwrap_or(false);
        if should_consume {
            env.consume(&var)?;
        }
    }
    Ok(())
}

impl Type {
    fn sender(payload: Type) -> Self {
        Type::Sender(Box::new(payload))
    }

    fn receiver(payload: Type) -> Self {
        Type::Receiver(Box::new(payload))
    }

    fn int_sender() -> Self {
        Type::sender(Type::Int)
    }

    fn int_receiver() -> Self {
        Type::receiver(Type::Int)
    }

    fn from_core(ty: &core::Type) -> Self {
        match ty {
            core::Type::Int => Type::Int,
            core::Type::Adt(name) => Type::Adt(name.clone()),
            core::Type::Sender(payload) => Type::sender(Type::from_core(payload)),
            core::Type::Receiver(payload) => Type::receiver(Type::from_core(payload)),
            core::Type::Func { .. } => Type::Int,
        }
    }

    fn payload_for_sender(&self) -> Option<&Type> {
        match self {
            Type::Sender(payload) => Some(payload),
            Type::Int | Type::Adt(_) | Type::Receiver(_) | Type::Unit => None,
        }
    }

    fn payload_for_receiver(&self) -> Option<&Type> {
        match self {
            Type::Receiver(payload) => Some(payload),
            Type::Int | Type::Adt(_) | Type::Sender(_) | Type::Unit => None,
        }
    }

    fn is_linear(&self) -> bool {
        matches!(self, Type::Adt(_) | Type::Sender(_) | Type::Receiver(_))
    }
}

fn block_external_vars(block: &Block) -> BTreeSet<String> {
    let mut locals = BTreeSet::new();
    let mut external = BTreeSet::new();
    for stmt in &block.statements {
        for var in stmt_used_vars(stmt) {
            if !locals.contains(&var) {
                external.insert(var);
            }
        }
        locals.extend(stmt_defined_vars(stmt));
    }
    external
}

fn stmt_used_vars(stmt: &Stmt) -> BTreeSet<String> {
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
        Stmt::Spawn(block) => block_external_vars(block),
        Stmt::While { cond, body } => {
            let mut vars = cond.free_vars();
            vars.extend(block_external_vars(body));
            vars
        }
        Stmt::If {
            cond,
            then_block,
            else_block,
        } => {
            let mut vars = cond.free_vars();
            vars.extend(block_external_vars(then_block));
            if let Some(else_block) = else_block {
                vars.extend(block_external_vars(else_block));
            }
            vars
        }
        Stmt::Match { scrutinee, arms } => {
            let mut vars = BTreeSet::from([scrutinee.clone()]);
            for arm in arms {
                let mut arm_vars = block_external_vars(&arm.block);
                for var in &arm.vars {
                    arm_vars.remove(var);
                }
                vars.extend(arm_vars);
            }
            vars
        }
    }
}

fn stmt_defined_vars(stmt: &Stmt) -> BTreeSet<String> {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sugar::ast::{AssignOp, BinaryOp, Binding, Block, Expr, MethodCall, Program, Stmt};
    use crate::sugar::parser;

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

    fn program(statements: Vec<Stmt>) -> Program {
        Program {
            adts: vec![],
            statements,
        }
    }

    fn assert_type_mismatch(result: Result<(), CheckError>, expected: Type, actual: Type) {
        assert_eq!(result, Err(CheckError::TypeMismatch { expected, actual }));
    }

    fn assert_use_after_consume(result: Result<(), CheckError>, expected: &str) {
        assert_eq!(
            result,
            Err(CheckError::UseAfterConsume {
                var: expected.to_string()
            })
        );
    }

    #[test]
    fn accepts_well_typed_program() {
        let program = program(vec![
            Stmt::LetChannel {
                payload: core::Type::Int,
                sender: "s".to_string(),
                receiver: "r".to_string(),
            },
            Stmt::Expr(Expr::MethodCall {
                receiver: Box::new(var("s")),
                method: MethodCall::Send(Box::new(int(1))),
            }),
            Stmt::Let {
                binding: binding("v"),
                value: Expr::MethodCall {
                    receiver: Box::new(var("r")),
                    method: MethodCall::Recv,
                },
            },
            Stmt::Assert(Expr::BinaryOp {
                lhs: Box::new(var("v")),
                op: BinaryOp::Eq,
                rhs: Box::new(int(1)),
            }),
            Stmt::Expr(Expr::MethodCall {
                receiver: Box::new(var("s")),
                method: MethodCall::Drop,
            }),
            Stmt::Expr(Expr::MethodCall {
                receiver: Box::new(var("r")),
                method: MethodCall::Drop,
            }),
        ]);

        assert_eq!(check_program(&program), Ok(()));
    }

    #[test]
    fn accepts_undefined_variable_as_external_int() {
        let program = program(vec![Stmt::Assert(var("x"))]);

        assert_eq!(check_program(&program), Ok(()));
    }

    #[test]
    fn accepts_assignment_to_undeclared_int_variable() {
        let program = program(vec![Stmt::Assign {
            target: "x".to_string(),
            op: AssignOp::Assign,
            value: int(1),
        }]);

        assert_eq!(check_program(&program), Ok(()));
    }

    #[test]
    fn accepts_channel_payload_send_and_recv() {
        let program = program(vec![
            Stmt::LetChannel {
                payload: core::Type::int_sender(),
                sender: "s".to_string(),
                receiver: "r".to_string(),
            },
            Stmt::LetChannel {
                payload: core::Type::Int,
                sender: "inner_s".to_string(),
                receiver: "inner_r".to_string(),
            },
            Stmt::Expr(Expr::MethodCall {
                receiver: Box::new(var("s")),
                method: MethodCall::Send(Box::new(var("inner_s"))),
            }),
            Stmt::Let {
                binding: binding("received_s"),
                value: Expr::MethodCall {
                    receiver: Box::new(var("r")),
                    method: MethodCall::Recv,
                },
            },
            Stmt::Expr(Expr::MethodCall {
                receiver: Box::new(var("received_s")),
                method: MethodCall::Send(Box::new(int(1))),
            }),
        ]);

        assert_eq!(check_program(&program), Ok(()));
    }

    #[test]
    fn rejects_use_after_sending_linear_payload() {
        let program = program(vec![
            Stmt::LetChannel {
                payload: core::Type::int_sender(),
                sender: "s".to_string(),
                receiver: "r".to_string(),
            },
            Stmt::LetChannel {
                payload: core::Type::Int,
                sender: "inner_s".to_string(),
                receiver: "inner_r".to_string(),
            },
            Stmt::Expr(Expr::MethodCall {
                receiver: Box::new(var("s")),
                method: MethodCall::Send(Box::new(var("inner_s"))),
            }),
            Stmt::Expr(Expr::MethodCall {
                receiver: Box::new(var("inner_s")),
                method: MethodCall::Drop,
            }),
        ]);

        assert_use_after_consume(check_program(&program), "inner_s");
    }

    #[test]
    fn rejects_undefined_variable_used_as_sender() {
        let program = program(vec![Stmt::Expr(Expr::MethodCall {
            receiver: Box::new(var("x")),
            method: MethodCall::Send(Box::new(int(1))),
        })]);

        assert_type_mismatch(check_program(&program), Type::int_sender(), Type::Int);
    }

    #[test]
    fn rejects_send_to_receiver() {
        let program = program(vec![
            Stmt::LetChannel {
                payload: core::Type::Int,
                sender: "s".to_string(),
                receiver: "r".to_string(),
            },
            Stmt::Expr(Expr::MethodCall {
                receiver: Box::new(var("r")),
                method: MethodCall::Send(Box::new(int(1))),
            }),
        ]);

        assert_type_mismatch(
            check_program(&program),
            Type::int_sender(),
            Type::int_receiver(),
        );
    }

    #[test]
    fn rejects_recv_from_sender() {
        let program = program(vec![
            Stmt::LetChannel {
                payload: core::Type::Int,
                sender: "s".to_string(),
                receiver: "r".to_string(),
            },
            Stmt::Let {
                binding: binding("v"),
                value: Expr::MethodCall {
                    receiver: Box::new(var("s")),
                    method: MethodCall::Recv,
                },
            },
        ]);

        assert_type_mismatch(
            check_program(&program),
            Type::int_receiver(),
            Type::int_sender(),
        );
    }

    #[test]
    fn rejects_non_int_send_payload() {
        let program = program(vec![
            Stmt::LetChannel {
                payload: core::Type::Int,
                sender: "s".to_string(),
                receiver: "r".to_string(),
            },
            Stmt::Expr(Expr::MethodCall {
                receiver: Box::new(var("s")),
                method: MethodCall::Send(Box::new(var("s"))),
            }),
        ]);

        assert_type_mismatch(check_program(&program), Type::Int, Type::int_sender());
    }

    #[test]
    fn rejects_arithmetic_on_non_int_values() {
        let program = program(vec![
            Stmt::LetChannel {
                payload: core::Type::Int,
                sender: "s".to_string(),
                receiver: "r".to_string(),
            },
            Stmt::Let {
                binding: binding("x"),
                value: Expr::BinaryOp {
                    lhs: Box::new(var("s")),
                    op: BinaryOp::Add,
                    rhs: Box::new(int(1)),
                },
            },
        ]);

        assert_type_mismatch(check_program(&program), Type::Int, Type::int_sender());
    }

    #[test]
    fn rejects_assert_on_non_int_value() {
        let program = program(vec![
            Stmt::LetChannel {
                payload: core::Type::Int,
                sender: "s".to_string(),
                receiver: "r".to_string(),
            },
            Stmt::Assert(var("s")),
        ]);

        assert_type_mismatch(check_program(&program), Type::Int, Type::int_sender());
    }

    #[test]
    fn rejects_use_after_drop() {
        let program = program(vec![
            Stmt::LetChannel {
                payload: core::Type::Int,
                sender: "s".to_string(),
                receiver: "r".to_string(),
            },
            Stmt::Expr(Expr::MethodCall {
                receiver: Box::new(var("s")),
                method: MethodCall::Drop,
            }),
            Stmt::Expr(Expr::MethodCall {
                receiver: Box::new(var("s")),
                method: MethodCall::Send(Box::new(int(1))),
            }),
        ]);

        assert_use_after_consume(check_program(&program), "s");
    }

    #[test]
    fn rejects_parent_use_after_spawn_consumes_linear_variable() {
        let program = program(vec![
            Stmt::LetChannel {
                payload: core::Type::Int,
                sender: "s".to_string(),
                receiver: "r".to_string(),
            },
            Stmt::Spawn(Block {
                statements: vec![Stmt::Expr(Expr::MethodCall {
                    receiver: Box::new(var("s")),
                    method: MethodCall::Send(Box::new(int(1))),
                })],
            }),
            Stmt::Expr(Expr::MethodCall {
                receiver: Box::new(var("s")),
                method: MethodCall::Drop,
            }),
        ]);

        assert_use_after_consume(check_program(&program), "s");
    }

    #[test]
    fn accepts_adt_constructor_and_match() {
        let program = parser::parse_program(
            r#"
            data Box = Hold(Sender<int>)
            let s, r = channel();
            let b = Box::Hold(s);
            match b {
              Box::Hold(s2) => {
                s2.drop();
                r.drop();
              }
            }
            "#,
        )
        .expect("ADT program should parse");

        assert_eq!(check_program(&program), Ok(()));
    }

    #[test]
    fn accepts_adt_equality_assertion_against_constructor_pattern() {
        let program = parser::parse_program(
            r#"
            data Option = Some(int) | None
            let s, r = channel<Option>();
            s.send(Option::Some(42));
            let x = r.recv();
            assert!(x == Option::Some(42));
            "#,
        )
        .expect("ADT equality program should parse");

        assert_eq!(check_program(&program), Ok(()));
    }

    #[test]
    fn rejects_use_after_adt_equality_assertion() {
        let program = parser::parse_program(
            r#"
            data Option = Some(int) | None
            let x = Option::Some(42);
            assert!(x == Option::Some(42));
            x.drop();
            "#,
        )
        .expect("ADT equality program should parse");

        assert_use_after_consume(check_program(&program), "x");
    }

    #[test]
    fn rejects_duplicate_linear_variable_in_constructor_arguments() {
        let program = parser::parse_program(
            r#"
            data Pair = Both(Sender<int>, Sender<int>)
            let s, r = channel();
            let p = Pair::Both(s, s);
            "#,
        )
        .expect("ADT program should parse");

        assert_use_after_consume(check_program(&program), "s");
    }

    #[test]
    fn rejects_adt_equality_outside_assert_lowering() {
        let program = parser::parse_program(
            r#"
            data Option = Some(int) | None
            let x = Option::Some(1);
            if (x == Option::Some(1)) {
            }
            "#,
        )
        .expect("ADT equality program should parse");

        assert_type_mismatch(
            check_program(&program),
            Type::Int,
            Type::Adt("Option".to_string()),
        );
    }

    #[test]
    fn rejects_use_after_moving_linear_value_into_adt() {
        let program = parser::parse_program(
            r#"
            data Box = Hold(Sender<int>)
            let s, r = channel();
            let b = Box::Hold(s);
            s.drop();
            "#,
        )
        .expect("ADT program should parse");

        assert_use_after_consume(check_program(&program), "s");
    }

    #[test]
    fn rejects_use_after_matching_adt() {
        let program = parser::parse_program(
            r#"
            data Box = Empty
            let b = Box::Empty();
            match b {
              Box::Empty() => {}
            }
            b.drop();
            "#,
        )
        .expect("ADT program should parse");

        assert_use_after_consume(check_program(&program), "b");
    }

    #[test]
    fn rejects_constructor_field_type_mismatch() {
        let program = parser::parse_program(
            r#"
            data Box = Hold(Sender<int>)
            let x = 1;
            let b = Box::Hold(x);
            "#,
        )
        .expect("ADT program should parse");

        assert_type_mismatch(check_program(&program), Type::int_sender(), Type::Int);
    }
}

use std::collections::{BTreeSet, HashMap};

use crate::core::ast as core;

use super::ast::{AssignOp, BinaryOp, Block, Expr, MethodCall, Program, Stmt};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Int,
    Sender(Box<Type>),
    Receiver(Box<Type>),
    Unit,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CheckError {
    UndefinedVariable { var: String },
    TypeMismatch { expected: Type, actual: Type },
    UseAfterConsume { var: String },
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
    let mut env = Env::default();
    check_stmts(&program.statements, &mut env)
}

fn check_stmts(stmts: &[Stmt], env: &mut Env) -> Result<(), CheckError> {
    for stmt in stmts {
        check_stmt(stmt, env)?;
    }
    Ok(())
}

fn check_stmt(stmt: &Stmt, env: &mut Env) -> Result<(), CheckError> {
    match stmt {
        Stmt::Let { binding, value } => {
            let ty = check_expr(value, env)?;
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
            let value_ty = check_expr(value, env)?;
            expect_type(Type::Int, value_ty)?;
            if !matches!(op, AssignOp::Assign) {
                expect_var_type(env, target, Type::Int)?;
            }
            Ok(())
        }
        Stmt::Expr(expr) => {
            check_expr(expr, env)?;
            Ok(())
        }
        Stmt::Call { args, .. } => {
            for arg in args {
                let ty = check_expr(arg, env)?;
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
            check_block(block, &mut child_env)?;
            for var in moved_vars {
                env.consume(&var)?;
            }
            Ok(())
        }
        Stmt::While { cond, body } => {
            let cond_ty = check_expr(cond, env)?;
            expect_type(Type::Int, cond_ty)?;
            let mut body_env = env.clone();
            check_block(body, &mut body_env)?;
            Ok(())
        }
        Stmt::If {
            cond,
            then_block,
            else_block,
        } => {
            let cond_ty = check_expr(cond, env)?;
            expect_type(Type::Int, cond_ty)?;
            let mut then_env = env.clone();
            check_block(then_block, &mut then_env)?;
            if let Some(else_block) = else_block {
                let mut else_env = env.clone();
                check_block(else_block, &mut else_env)?;
            }
            Ok(())
        }
        Stmt::Assert(expr) => {
            let ty = check_expr(expr, env)?;
            expect_type(Type::Int, ty)
        }
    }
}

fn check_block(block: &Block, env: &mut Env) -> Result<(), CheckError> {
    check_stmts(&block.statements, env)
}

fn check_expr(expr: &Expr, env: &mut Env) -> Result<Type, CheckError> {
    match expr {
        Expr::Int(_) => Ok(Type::Int),
        Expr::Var(var) => env.ty_of(var),
        Expr::MethodCall { receiver, method } => check_method_call(receiver, method, env),
        Expr::BinaryOp { lhs, op, rhs } => {
            let lhs_ty = check_expr(lhs, env)?;
            expect_type(Type::Int, lhs_ty)?;
            let rhs_ty = check_expr(rhs, env)?;
            expect_type(Type::Int, rhs_ty)?;
            match op {
                BinaryOp::Add
                | BinaryOp::Sub
                | BinaryOp::Mul
                | BinaryOp::Eq
                | BinaryOp::Ne
                | BinaryOp::Lt
                | BinaryOp::Le
                | BinaryOp::Gt
                | BinaryOp::Ge => Ok(Type::Int),
            }
        }
    }
}

fn check_method_call(
    receiver: &Expr,
    method: &MethodCall,
    env: &mut Env,
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
            let value_ty = check_expr(value, env)?;
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
            core::Type::Sender(payload) => Type::sender(Type::from_core(payload)),
            core::Type::Receiver(payload) => Type::receiver(Type::from_core(payload)),
            core::Type::Func { .. } => Type::Int,
        }
    }

    fn payload_for_sender(&self) -> Option<&Type> {
        match self {
            Type::Sender(payload) => Some(payload),
            Type::Int | Type::Receiver(_) | Type::Unit => None,
        }
    }

    fn payload_for_receiver(&self) -> Option<&Type> {
        match self {
            Type::Receiver(payload) => Some(payload),
            Type::Int | Type::Sender(_) | Type::Unit => None,
        }
    }

    fn is_linear(&self) -> bool {
        matches!(self, Type::Sender(_) | Type::Receiver(_))
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
        | Stmt::Assert(_) => BTreeSet::new(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sugar::ast::{AssignOp, BinaryOp, Binding, Block, Expr, MethodCall, Program, Stmt};

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
        Program { statements }
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
}

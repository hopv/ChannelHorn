use std::collections::BTreeSet;

pub type VarName = String;
pub type FuncName = String;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Program {
    pub statements: Vec<Stmt>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Block {
    pub statements: Vec<Stmt>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Stmt {
    Let {
        binding: Binding,
        value: Expr,
    },
    LetChannel {
        sender: VarName,
        receiver: VarName,
    },
    Assign {
        target: VarName,
        op: AssignOp,
        value: Expr,
    },
    Expr(Expr),
    Call {
        name: FuncName,
        args: Vec<Expr>,
    },
    Spawn(Block),
    While {
        cond: Expr,
        body: Block,
    },
    If {
        cond: Expr,
        then_block: Block,
        else_block: Option<Block>,
    },
    Assert(Expr),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Binding {
    pub var: VarName,
}

impl Binding {
    pub fn vars(&self) -> Vec<&VarName> {
        vec![&self.var]
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AssignOp {
    Assign,
    AddAssign,
    SubAssign,
    MulAssign,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Int(i32),
    Var(VarName),
    MethodCall {
        receiver: Box<Expr>,
        method: MethodCall,
    },
    BinaryOp {
        lhs: Box<Expr>,
        op: BinaryOp,
        rhs: Box<Expr>,
    },
}

impl Stmt {
    pub fn free_vars(&self) -> BTreeSet<VarName> {
        let mut vars = BTreeSet::new();
        match self {
            Stmt::Let { value, .. } => {
                vars.extend(value.free_vars());
            }
            Stmt::LetChannel { .. } => {}
            Stmt::Assign { target, op, value } => {
                if !matches!(op, AssignOp::Assign) {
                    vars.insert(target.clone());
                }
                vars.extend(value.free_vars());
            }
            Stmt::Expr(expr) | Stmt::Assert(expr) => {
                vars.extend(expr.free_vars());
            }
            Stmt::Call { args, .. } => {
                for arg in args {
                    vars.extend(arg.free_vars());
                }
            }
            Stmt::Spawn(block) => {
                for stmt in &block.statements {
                    vars.extend(stmt.free_vars());
                }
            }
            Stmt::While { cond, body } => {
                vars.extend(cond.free_vars());
                for stmt in &body.statements {
                    vars.extend(stmt.free_vars());
                }
            }
            Stmt::If {
                cond,
                then_block,
                else_block,
            } => {
                vars.extend(cond.free_vars());
                for stmt in &then_block.statements {
                    vars.extend(stmt.free_vars());
                }
                if let Some(else_block) = else_block {
                    for stmt in &else_block.statements {
                        vars.extend(stmt.free_vars());
                    }
                }
            }
        }
        vars
    }
}

impl Expr {
    pub fn free_vars(&self) -> BTreeSet<VarName> {
        let mut vars = BTreeSet::new();
        self.collect_free_vars(&mut vars);
        vars
    }

    fn collect_free_vars(&self, vars: &mut BTreeSet<VarName>) {
        match self {
            Expr::Int(_) => {}
            Expr::Var(var) => {
                vars.insert(var.clone());
            }
            Expr::MethodCall { receiver, method } => {
                receiver.collect_free_vars(vars);
                method.collect_free_vars(vars);
            }
            Expr::BinaryOp { lhs, rhs, .. } => {
                lhs.collect_free_vars(vars);
                rhs.collect_free_vars(vars);
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MethodCall {
    Send(Box<Expr>),
    Recv,
    Drop,
    Clone,
}

impl MethodCall {
    fn collect_free_vars(&self, vars: &mut BTreeSet<VarName>) {
        match self {
            MethodCall::Send(value) => value.collect_free_vars(vars),
            MethodCall::Recv | MethodCall::Drop | MethodCall::Clone => {}
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn binding(name: &str) -> Binding {
        Binding {
            var: name.to_string(),
        }
    }

    fn var(name: &str) -> Expr {
        Expr::Var(name.to_string())
    }

    fn vars(names: &[&str]) -> BTreeSet<VarName> {
        names.iter().map(|name| name.to_string()).collect()
    }

    #[test]
    fn represents_channel_example() {
        let program = Program {
            statements: vec![
                Stmt::LetChannel {
                    sender: "s".to_string(),
                    receiver: "r".to_string(),
                },
                Stmt::Expr(Expr::MethodCall {
                    receiver: Box::new(var("s")),
                    method: MethodCall::Send(Box::new(Expr::Int(1))),
                }),
                Stmt::Let {
                    binding: binding("v"),
                    value: Expr::MethodCall {
                        receiver: Box::new(var("r")),
                        method: MethodCall::Recv,
                    },
                },
                Stmt::Expr(Expr::MethodCall {
                    receiver: Box::new(var("s")),
                    method: MethodCall::Drop,
                }),
            ],
        };

        assert_eq!(program.statements.len(), 4);
        assert_eq!(
            program.statements[0],
            Stmt::LetChannel {
                sender: "s".to_string(),
                receiver: "r".to_string(),
            }
        );
    }

    #[test]
    fn let_binding_contains_single_variable() {
        let stmt = Stmt::Let {
            binding: binding("value"),
            value: Expr::Int(1),
        };

        assert_eq!(
            stmt,
            Stmt::Let {
                binding: Binding {
                    var: "value".to_string()
                },
                value: Expr::Int(1),
            }
        );
    }

    #[test]
    fn binding_vars_contains_single_variable() {
        let binding = binding("value");

        assert_eq!(binding.vars(), vec![&"value".to_string()]);
    }

    #[test]
    fn expression_free_vars_include_receiver_and_arguments() {
        let expr = Expr::MethodCall {
            receiver: Box::new(var("s")),
            method: MethodCall::Send(Box::new(Expr::BinaryOp {
                lhs: Box::new(var("v")),
                op: BinaryOp::Add,
                rhs: Box::new(Expr::Int(1)),
            })),
        };

        assert_eq!(expr.free_vars(), vars(&["s", "v"]));
    }

    #[test]
    fn call_function_name_is_not_a_free_var() {
        let stmt = Stmt::Call {
            name: "assert".to_string(),
            args: vec![Expr::BinaryOp {
                lhs: Box::new(var("lhs")),
                op: BinaryOp::Eq,
                rhs: Box::new(var("rhs")),
            }],
        };

        assert_eq!(stmt.free_vars(), vars(&["lhs", "rhs"]));
    }
}

use std::collections::HashMap;

pub type FuncName = String;
pub type VarName = String;

#[derive(Debug, Clone)]
pub struct Program {
    pub functions: HashMap<FuncName, Function>,
    pub init: FuncCall,
}

#[derive(Debug, Clone)]
pub struct Function {
    pub name: FuncName,
    pub params: Vec<(VarName, Type)>,
    pub body: Statement,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Int,
    Sender,
    Receiver,
    Func { params: Vec<Type> },
}

impl Type {
    pub fn is_linear(&self) -> bool {
        match self {
            Type::Int => false,
            Type::Sender => true,
            Type::Receiver => true,
            Type::Func { params: _ } => false,
        }
    }
}

#[derive(Debug, Clone)]
pub enum Statement {
    Fail,
    Unit,
    Call(FuncCall),
    If(Expr, FuncCall, FuncCall),
    Spawn(FuncCall, FuncCall),
    New {
        sender: VarName,
        receiver: VarName,
        body: FuncCall,
    },
    Send {
        sender: VarName,
        value: Expr,
        body: FuncCall,
    },
    Recv {
        receiver: VarName,
        var: VarName,
        body: FuncCall,
    },
    Dup {
        sender: VarName,
        var: VarName,
        body: FuncCall,
    },
}

impl Statement {
    pub fn substitute_var(&mut self, var_map: &HashMap<VarName, VarName>) {
        match self {
            Statement::Fail | Statement::Unit => {}
            Statement::Call(call) => {
                call.substitute_var(var_map);
            }
            Statement::If(cond, then_call, else_call) => {
                cond.substitute_var(var_map);
                then_call.substitute_var(var_map);
                else_call.substitute_var(var_map);
            }
            Statement::Spawn(call1, call2) => {
                call1.substitute_var(var_map);
                call2.substitute_var(var_map);
            }
            Statement::New { body, .. } => {
                body.substitute_var(var_map);
            }
            Statement::Send {
                sender,
                value,
                body,
            } => {
                if let Some(new_sender) = var_map.get(sender) {
                    *sender = new_sender.clone();
                }
                value.substitute_var(var_map);
                body.substitute_var(var_map);
            }
            Statement::Recv { receiver, body, .. } => {
                if let Some(new_receiver) = var_map.get(receiver) {
                    *receiver = new_receiver.clone();
                }
                body.substitute_var(var_map);
            }
            Statement::Dup { body, sender, .. } => {
                if let Some(new_sender) = var_map.get(sender) {
                    *sender = new_sender.clone();
                }
                body.substitute_var(var_map);
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct FuncCall {
    pub name: FuncName,
    pub args: Vec<Expr>,
}

impl FuncCall {
    pub fn substitute_var(&mut self, var_map: &HashMap<VarName, VarName>) {
        for arg in &mut self.args {
            arg.substitute_var(var_map);
        }
    }

    pub fn free_vars(&self) -> Vec<VarName> {
        let mut vars = vec![];
        for arg in &self.args {
            vars.extend(arg.free_vars());
        }
        vars
    }
}

#[derive(Debug, Clone)]
pub enum Expr {
    Num(i32),
    Var(VarName),
    Op(Box<Expr>, OpKind, Box<Expr>),
}

impl Expr {
    pub fn substitute_var(&mut self, var_map: &HashMap<VarName, VarName>) {
        match self {
            Expr::Num(_) => {}
            Expr::Var(v) => {
                if let Some(new_v) = var_map.get(v) {
                    *v = new_v.clone();
                }
            }
            Expr::Op(lhs, _, rhs) => {
                lhs.substitute_var(var_map);
                rhs.substitute_var(var_map);
            }
        }
    }

    pub fn free_vars(&self) -> Vec<VarName> {
        match self {
            Expr::Num(_) => vec![],
            Expr::Var(v) => vec![v.clone()],
            Expr::Op(lhs, _, rhs) => {
                let mut vars = lhs.free_vars();
                vars.extend(rhs.free_vars());
                vars
            }
        }
    }
}

#[derive(Debug, Clone)]
pub enum OpKind {
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

use std::collections::HashMap;

pub type FuncName = String;
pub type TypeName = String;
pub type VarName = String;
pub type VariantName = String;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Program {
    pub adts: Vec<AdtDef>,
    pub functions: HashMap<FuncName, Function>,
    pub init: FuncCall,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AdtDef {
    pub name: TypeName,
    pub variants: Vec<VariantDef>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VariantDef {
    pub name: VariantName,
    pub fields: Vec<Type>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Function {
    pub name: FuncName,
    pub params: Vec<(VarName, Type)>,
    pub body: Statement,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Int,
    Adt(TypeName),
    Sender(Box<Type>),
    Receiver(Box<Type>),
    Func { params: Vec<Type> },
}

impl Type {
    pub fn sender(payload: Type) -> Self {
        Type::Sender(Box::new(payload))
    }

    pub fn receiver(payload: Type) -> Self {
        Type::Receiver(Box::new(payload))
    }

    pub fn int_sender() -> Self {
        Type::sender(Type::Int)
    }

    pub fn int_receiver() -> Self {
        Type::receiver(Type::Int)
    }

    pub fn payload(&self) -> Option<&Type> {
        match self {
            Type::Sender(payload) | Type::Receiver(payload) => Some(payload),
            Type::Int | Type::Adt(_) | Type::Func { .. } => None,
        }
    }

    pub fn is_linear(&self) -> bool {
        match self {
            Type::Int => false,
            Type::Adt(_) => true,
            Type::Sender(_) => true,
            Type::Receiver(_) => true,
            Type::Func { params: _ } => false,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Statement {
    Fail,
    Unit,
    Call(FuncCall),
    If(Expr, FuncCall, FuncCall),
    Spawn(FuncCall, FuncCall),
    New {
        payload: Type,
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
    Match {
        scrutinee: VarName,
        arms: Vec<MatchArm>,
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
            Statement::Match { scrutinee, arms } => {
                if let Some(new_scrutinee) = var_map.get(scrutinee) {
                    *scrutinee = new_scrutinee.clone();
                }
                for arm in arms {
                    let mut body_var_map = var_map.clone();
                    for var in &arm.vars {
                        body_var_map.remove(var);
                    }
                    arm.body.substitute_var(&body_var_map);
                }
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MatchArm {
    pub type_name: TypeName,
    pub variant: VariantName,
    pub vars: Vec<VarName>,
    pub body: FuncCall,
}

#[derive(Debug, Clone, PartialEq, Eq)]
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Num(i32),
    Var(VarName),
    Ctor {
        type_name: TypeName,
        variant: VariantName,
        args: Vec<Expr>,
    },
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
            Expr::Ctor { args, .. } => {
                for arg in args {
                    arg.substitute_var(var_map);
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
            Expr::Ctor { args, .. } => args.iter().flat_map(Expr::free_vars).collect(),
            Expr::Op(lhs, _, rhs) => {
                let mut vars = lhs.free_vars();
                vars.extend(rhs.free_vars());
                vars
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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

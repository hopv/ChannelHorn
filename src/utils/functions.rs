use crate::ast::{Expr, FuncCall, Function, Statement, Type};

pub fn gen_assert() -> Function {
    Function {
        name: "assert".to_string(),
        params: vec![("cond".to_string(), Type::Int)],
        body: Statement::If(
            Expr::Var("cond".to_string()),
            FuncCall {
                name: "unit".to_string(),
                args: vec![],
            },
            FuncCall {
                name: "fail".to_string(),
                args: vec![],
            },
        ),
    }
}

pub fn gen_unit() -> Function {
    Function {
        name: "unit".to_string(),
        params: vec![],
        body: Statement::Unit,
    }
}

pub fn gen_fail() -> Function {
    Function {
        name: "fail".to_string(),
        params: vec![],
        body: Statement::Fail,
    }
}

pub fn gen_send_fun() -> Function {
    Function {
        name: "send_fun".to_string(),
        params: vec![
            ("sender".to_string(), Type::Sender),
            ("value".to_string(), Type::Int),
        ],
        body: Statement::Send {
            sender: "sender".to_string(),
            value: Expr::Var("value".to_string()),
            body: FuncCall {
                name: "unit".to_string(),
                args: vec![],
            },
        },
    }
}

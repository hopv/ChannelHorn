use std::collections::HashMap;

use anyhow::{anyhow, bail, Result};

use crate::ast::{Expr, FuncCall, Function, OpKind, Program, Statement, Type};

peg::parser! {
    grammar channel_parser() for str {
        pub rule program() -> (Option<FuncCall>, Vec<Function>)
            = _ init:init_clause()? funcs:(function_def() ++ _) _ { (init, funcs) }

        rule init_clause() -> FuncCall
            = kw_init() assign()? call:func_call() { call }

        rule function_def() -> Function
            = name:ident() lparen() params:param_list()? rparen() assign() body:statement() {
                Function {
                    name,
                    params: params.unwrap_or_default(),
                    body,
                }
            }

        rule param_list() -> Vec<(String, Type)>
            = params:(param() ** comma()) { params }

        rule param() -> (String, Type)
            = name:ident() colon() ty:type_() { (name, ty) }

        rule statement() -> Statement
            = spawn_stmt()
            / if_stmt()
            / new_stmt()
            / send_stmt()
            / let_recv_stmt()
            / let_dup_stmt()
            / unit_stmt()
            / fail_stmt()
            / call_stmt()

        rule spawn_stmt() -> Statement
            = kw_spawn() lparen() first:func_call() rparen() semi() second:func_call() {
                Statement::Spawn(first, second)
            }

        rule if_stmt() -> Statement
            = kw_if() cond:expression() kw_then() then_call:func_call() kw_else() else_call:func_call() {
                Statement::If(cond, then_call, else_call)
            }

        rule new_stmt() -> Statement
            = kw_new() sender:ident() comma() receiver:ident() kw_in() body:func_call() {
                Statement::New { sender, receiver, body }
            }

        rule send_stmt() -> Statement
            = kw_send() value:expression() kw_to() sender:ident() semi() body:func_call() {
                Statement::Send { sender, value, body }
            }

        rule let_recv_stmt() -> Statement
            = kw_let() var:ident() assign() kw_recv() receiver:ident() kw_in() body:func_call() {
                Statement::Recv { receiver, var, body }
            }

        rule let_dup_stmt() -> Statement
            = kw_let() var:ident() assign() kw_dup() sender:ident() kw_in() body:func_call() {
                Statement::Dup { sender, var, body }
            }

        rule unit_stmt() -> Statement
            = lparen() rparen() { Statement::Unit }

        rule fail_stmt() -> Statement
            = kw_fail_literal() { Statement::Fail }

        rule call_stmt() -> Statement
            = call:func_call() { Statement::Call(call) }

        rule func_call() -> FuncCall
            = name:ident() lparen() args:(expression() ** comma())? rparen() {
                FuncCall {
                    name,
                    args: args.unwrap_or_default(),
                }
            }

        rule expression() -> Expr
            = equality()

        rule equality() -> Expr
            = first:comparison() rest:(op:equality_op() right:comparison() { (op, right) })* {
                rest.into_iter().fold(first, |acc, (op, expr)| {
                    Expr::Op(Box::new(acc), op, Box::new(expr))
                })
            }

        rule comparison() -> Expr
            = first:addition() rest:(op:comparison_op() right:addition() { (op, right) })* {
                rest.into_iter().fold(first, |acc, (op, expr)| {
                    Expr::Op(Box::new(acc), op, Box::new(expr))
                })
            }

        rule addition() -> Expr
            = first:multiplication() rest:(op:add_op() right:multiplication() { (op, right) })* {
                rest.into_iter().fold(first, |acc, (op, expr)| {
                    Expr::Op(Box::new(acc), op, Box::new(expr))
                })
            }

        rule multiplication() -> Expr
            = first:term() rest:(op:mul_op() right:term() { (op, right) })* {
                rest.into_iter().fold(first, |acc, (op, expr)| {
                    Expr::Op(Box::new(acc), op, Box::new(expr))
                })
            }

        rule term() -> Expr
            = number()
            / variable()
            / lparen() expr:expression() rparen() { expr }

        rule equality_op() -> OpKind
            = eqeq() { OpKind::Eq }
            / noteq() { OpKind::Ne }

        rule comparison_op() -> OpKind
            = le() { OpKind::Le }
            / lt() { OpKind::Lt }
            / ge() { OpKind::Ge }
            / gt() { OpKind::Gt }

        rule add_op() -> OpKind
            = plus() { OpKind::Add }
            / minus() { OpKind::Sub }

        rule mul_op() -> OpKind
            = star() { OpKind::Mul }

        rule variable() -> Expr
            = name:ident() { Expr::Var(name) }

        rule number() -> Expr
            = s:$("-"? ['0'..='9']+) _() {
                let value: i32 = s.parse().expect("valid integer literal");
                Expr::Num(value)
            }

        rule type_() -> Type
            = sender_type()
            / receiver_type()
            / int_type()

        rule sender_type() -> Type
            = quiet!{ "Sender" }
              !ident_char() _() { Type::Sender }

        rule receiver_type() -> Type
            = quiet!{ "Receiver" }
            !ident_char() _() { Type::Receiver }

        rule int_type() -> Type
            = quiet!{ "int" }
              !ident_char() _() { Type::Int }

        rule ident() -> String
            = s:$((ident_start()) (ident_char())*) _() { s.to_string() }

        rule ident_start()
            = ['a'..='z' | 'A'..='Z' | '_']

        rule ident_char()
            = ['a'..='z' | 'A'..='Z' | '0'..='9' | '_']

        rule kw_init()
            = quiet!{ "init" } !ident_char() _()

        rule kw_spawn()
            = quiet!{ "spawn" } !ident_char() _()

        rule kw_if()
            = quiet!{ "if" } !ident_char() _()

        rule kw_then()
            = quiet!{ "then" } !ident_char() _()

        rule kw_else()
            = quiet!{ "else" } !ident_char() _()

        rule kw_new()
            = quiet!{ "new" } !ident_char() _()

        rule kw_in()
            = quiet!{ "in" } !ident_char() _()

        rule kw_send()
            = quiet!{ "send" } !ident_char() _()

        rule kw_to()
            = quiet!{ "to" } !ident_char() _()

        rule kw_let()
            = quiet!{ "let" } !ident_char() _()

        rule kw_recv()
            = quiet!{ "recv" } !ident_char() _()

        rule kw_dup()
            = quiet!{ "dup" } !ident_char() _()

        rule kw_fail_literal()
            = quiet!{ "fail" } !ident_char() !['('] _()

        rule lparen()
            = quiet!{ "(" } _()

        rule rparen()
            = quiet!{ ")" } _()

        rule comma()
            = quiet!{ "," } _()

        rule colon()
            = quiet!{ ":" } _()

        rule assign()
            = quiet!{ "=" } _()

        rule semi()
            = quiet!{ ";" } _()

        rule plus()
            = quiet!{ "+" } _()

        rule minus()
            = quiet!{ "-" } _()

        rule star()
            = quiet!{ "*" } _()

        rule eqeq()
            = quiet!{ "==" } _()

        rule noteq()
            = quiet!{ "!=" } _()

        rule le()
            = quiet!{ "<=" } _()

        rule lt()
            = quiet!{ "<" } _()

        rule ge()
            = quiet!{ ">=" } _()

        rule gt()
            = quiet!{ ">" } _()

        rule whitespace()
            = [' ' | '\t' | '\r' | '\n']

        rule comment()
            = quiet!{
                "//" (!['\n'] [_])* ("\n" / "\r\n")?
            }
            / quiet!{
                "/*" (!("*/") [_])* "*/"
            }

        rule _
            = (whitespace() / comment())*
    }
}

pub fn parse_program(input: &str) -> Result<Program> {
    let (init_call, functions) =
        channel_parser::program(input).map_err(|e| anyhow!("parse error: {}", e))?;
    let mut map = HashMap::new();
    for func in functions {
        if map.contains_key(&func.name) {
            bail!("function '{}' is defined multiple times", func.name);
        }
        map.insert(func.name.clone(), func);
    }
    let init = match init_call {
        Some(call) => call,
        None => {
            if map.contains_key("main") {
                FuncCall {
                    name: "main".to_string(),
                    args: vec![],
                }
            } else {
                // bail!("init節がなく、main関数も存在しません");
                bail!("no init clause and no main function found")
            }
        }
    };
    Ok(Program {
        functions: map,
        init,
    })
}

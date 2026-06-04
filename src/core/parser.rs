use std::collections::HashMap;

use anyhow::{Result, anyhow};

use super::ast::{
    AdtDef, Expr, FuncCall, Function, MatchArm, OpKind, Program, Statement, Type, VariantDef,
};
use super::validate;

peg::parser! {
    grammar channel_parser() for str {
        pub rule program() -> (Vec<AdtDef>, FuncCall, Vec<Function>)
            = _ adts:adt_def()* init:init_clause() funcs:(function_def() ++ _) _ { (adts, init, funcs) }

        rule adt_def() -> AdtDef
            = kw_data() name:ident() assign() variants:(variant_def() ++ bar()) {
                AdtDef { name, variants }
            }

        rule variant_def() -> VariantDef
            = name:ident() fields:(lparen() fields:(type_() ** comma())? rparen() { fields.unwrap_or_default() })? {
                VariantDef {
                    name,
                    fields: fields.unwrap_or_default(),
                }
            }

        rule init_clause() -> FuncCall
            = kw_init() assign() call:func_call() { call }

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
            / match_stmt()
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

        rule match_stmt() -> Statement
            = kw_match() scrutinee:ident() lbrace() arms:(match_arm() ++ comma()) comma()? rbrace() {
                Statement::Match { scrutinee, arms }
            }

        rule match_arm() -> MatchArm
            = type_name:ident() double_colon() variant:ident() lparen() vars:(ident() ** comma())? rparen() arrow() body:func_call() {
                MatchArm {
                    type_name,
                    variant,
                    vars: vars.unwrap_or_default(),
                    body,
                }
            }

        rule new_stmt() -> Statement
            = kw_new() payload:generic_type_arg()? sender:ident() comma() receiver:ident() kw_in() body:func_call() {
                Statement::New {
                    payload: payload.unwrap_or(Type::Int),
                    sender,
                    receiver,
                    body,
                }
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
            / constructor()
            / variable()
            / lparen() expr:expression() rparen() { expr }

        rule constructor() -> Expr
            = type_name:ident() double_colon() variant:ident() lparen() args:(expression() ** comma())? rparen() {
                Expr::Ctor {
                    type_name,
                    variant,
                    args: args.unwrap_or_default(),
                }
            }

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
            / adt_type()

        rule sender_type() -> Type
            = quiet!{ "Sender" }
              payload:generic_type_arg()? !ident_char() _() {
                  Type::sender(payload.unwrap_or(Type::Int))
              }

        rule receiver_type() -> Type
            = quiet!{ "Receiver" }
              payload:generic_type_arg()? !ident_char() _() {
                  Type::receiver(payload.unwrap_or(Type::Int))
              }

        rule generic_type_arg() -> Type
            = lt() ty:type_() gt() { ty }

        rule int_type() -> Type
            = quiet!{ "int" }
              !ident_char() _() { Type::Int }

        rule adt_type() -> Type
            = name:ident() { Type::Adt(name) }

        rule ident() -> String
            = s:$((ident_start()) (ident_char())*) _() { s.to_string() }

        rule ident_start()
            = ['a'..='z' | 'A'..='Z' | '_']

        rule ident_char()
            = ['a'..='z' | 'A'..='Z' | '0'..='9' | '_']

        rule kw_init()
            = quiet!{ "init" } !ident_char() _()

        rule kw_data()
            = quiet!{ "data" } !ident_char() _()

        rule kw_match()
            = quiet!{ "match" } !ident_char() _()

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

        rule lbrace()
            = quiet!{ "{" } _()

        rule rbrace()
            = quiet!{ "}" } _()

        rule comma()
            = quiet!{ "," } _()

        rule bar()
            = quiet!{ "|" } _()

        rule colon()
            = quiet!{ ":" } _()

        rule double_colon()
            = quiet!{ "::" } _()

        rule arrow()
            = quiet!{ "=>" } _()

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
    let (adts, init, functions) =
        channel_parser::program(input).map_err(|e| anyhow!("parse error: {}", e))?;
    validate::validate_program_parts(&adts, &init, &functions)?;
    let mut map = HashMap::new();
    for func in functions {
        map.insert(func.name.clone(), func);
    }
    Ok(Program {
        adts,
        functions: map,
        init,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_line_comments_as_whitespace() {
        let program = parse_program(
            r#"
            // before init
            init = main() // after init

            // before function
            main() = () // before end of file
            "#,
        )
        .expect("line comments should parse as whitespace");

        assert_eq!(program.init.name, "main");
        assert_eq!(program.init.args, vec![]);
        assert_eq!(
            program
                .functions
                .get("main")
                .expect("main function should exist")
                .body,
            Statement::Unit
        );
    }

    #[test]
    fn parses_parameterized_channel_types() {
        let program = parse_program(
            r#"
            init = entry()

            entry() = ()
            main(s: Sender<int>, r: Receiver<int>) = ()
            "#,
        )
        .expect("parameterized channel types should parse");

        let main = program
            .functions
            .get("main")
            .expect("main function should exist");
        assert_eq!(
            main.params,
            vec![
                ("s".to_string(), Type::int_sender()),
                ("r".to_string(), Type::int_receiver()),
            ]
        );
    }

    #[test]
    fn parses_bare_channel_types_as_int_channels() {
        let program = parse_program(
            r#"
            init = entry()

            entry() = ()
            main(s: Sender, r: Receiver) = ()
            "#,
        )
        .expect("bare channel types should parse as int channels");

        let main = program
            .functions
            .get("main")
            .expect("main function should exist");
        assert_eq!(
            main.params,
            vec![
                ("s".to_string(), Type::int_sender()),
                ("r".to_string(), Type::int_receiver()),
            ]
        );
    }

    #[test]
    fn parses_new_payload_type_annotation() {
        let program = parse_program(
            r#"
            init = main()

            main() = new<Sender<int>> s, r in done(s, r)
            done(s: Sender<Sender<int>>, r: Receiver<Sender<int>>) = ()
            "#,
        )
        .expect("new payload type annotation should parse");

        let main = program
            .functions
            .get("main")
            .expect("main function should exist");
        assert_eq!(
            main.body,
            Statement::New {
                payload: Type::int_sender(),
                sender: "s".to_string(),
                receiver: "r".to_string(),
                body: FuncCall {
                    name: "done".to_string(),
                    args: vec![Expr::Var("s".to_string()), Expr::Var("r".to_string())],
                },
            }
        );
    }

    #[test]
    fn parses_adt_defs_constructors_and_match() {
        let program = parse_program(
            r#"
            data Option = None | Some(int)

            init = main()

            main() = use(Option::Some(1))
            use(opt: Option) = match opt {
                Option::None() => fail(),
                Option::Some(v) => done(v),
            }
            done(v: int) = ()
            fail() = fail
            "#,
        )
        .expect("ADT program should parse");

        assert_eq!(program.adts.len(), 1);
        assert_eq!(program.adts[0].name, "Option");
        assert_eq!(program.adts[0].variants[1].fields, vec![Type::Int]);

        let main = program
            .functions
            .get("main")
            .expect("main function should exist");
        assert_eq!(
            main.body,
            Statement::Call(FuncCall {
                name: "use".to_string(),
                args: vec![Expr::Ctor {
                    type_name: "Option".to_string(),
                    variant: "Some".to_string(),
                    args: vec![Expr::Num(1)],
                }],
            })
        );

        let use_func = program
            .functions
            .get("use")
            .expect("use function should exist");
        assert!(matches!(use_func.body, Statement::Match { .. }));
    }

    #[test]
    fn rejects_non_exhaustive_match() {
        let err = parse_program(
            r#"
            data Option = None | Some(int)

            init = main()

            main(opt: Option) = match opt {
                Option::None() => done(),
            }
            done() = ()
            "#,
        )
        .expect_err("non-exhaustive match should be rejected");

        assert!(err.to_string().contains("missing arm"));
    }
}

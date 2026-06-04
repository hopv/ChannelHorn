use std::collections::HashMap;

use anyhow::{Result, anyhow, bail};

use super::ast::{
    AdtDef, Expr, FuncCall, Function, MatchArm, Statement, Type, VarName, VariantDef,
};

#[derive(Debug, Clone)]
struct BindingState {
    ty: Type,
    consumed: bool,
}

#[derive(Debug, Clone, Default)]
struct Env {
    vars: HashMap<VarName, BindingState>,
}

impl Env {
    fn declare(&mut self, var: impl Into<VarName>, ty: Type) -> Result<()> {
        let var = var.into();
        if self.vars.contains_key(&var) {
            bail!("variable '{}' is already bound", var);
        }
        self.vars.insert(
            var,
            BindingState {
                ty,
                consumed: false,
            },
        );
        Ok(())
    }

    fn ensure_external_int(&mut self, var: &str) {
        self.vars.entry(var.to_string()).or_insert(BindingState {
            ty: Type::Int,
            consumed: false,
        });
    }

    fn get(&self, var: &str) -> Result<&BindingState> {
        let binding = self
            .vars
            .get(var)
            .ok_or_else(|| anyhow!("undefined variable '{}'", var))?;
        if binding.consumed {
            bail!("use after move of linear variable '{}'", var);
        }
        Ok(binding)
    }

    fn ty_of(&self, var: &str) -> Result<Type> {
        Ok(self.get(var)?.ty.clone())
    }

    fn consume_if_linear(&mut self, var: &str) -> Result<()> {
        let binding = self
            .vars
            .get_mut(var)
            .ok_or_else(|| anyhow!("undefined variable '{}'", var))?;
        if binding.consumed {
            bail!("use after move of linear variable '{}'", var);
        }
        if binding.ty.is_linear() {
            binding.consumed = true;
        }
        Ok(())
    }

    fn ensure_no_unconsumed_linear(&self) -> Result<()> {
        if let Some((var, _)) = self
            .vars
            .iter()
            .find(|(_, binding)| binding.ty.is_linear() && !binding.consumed)
        {
            bail!(
                "linear variable '{}' is not moved before non-terminal control transfer",
                var
            );
        }
        Ok(())
    }
}

#[derive(Debug, Clone)]
struct FunctionSig {
    params: Vec<Type>,
}

#[derive(Debug)]
struct Ctx<'a> {
    adts: HashMap<&'a str, &'a AdtDef>,
    functions: HashMap<&'a str, FunctionSig>,
}

pub fn validate_program_parts(
    adts: &[AdtDef],
    init: &FuncCall,
    functions: &[Function],
) -> Result<()> {
    validate_adts(adts)?;
    let ctx = Ctx {
        adts: adts.iter().map(|adt| (adt.name.as_str(), adt)).collect(),
        functions: function_sigs(functions)?,
    };

    for func in functions {
        validate_function(func, &ctx)?;
    }
    validate_init(init, &ctx)
}

fn function_sigs(functions: &[Function]) -> Result<HashMap<&str, FunctionSig>> {
    let mut sigs = HashMap::new();
    for func in functions {
        if sigs
            .insert(
                func.name.as_str(),
                FunctionSig {
                    params: func.params.iter().map(|(_, ty)| ty.clone()).collect(),
                },
            )
            .is_some()
        {
            bail!("function '{}' is defined multiple times", func.name);
        }
    }
    Ok(sigs)
}

fn validate_adts(adts: &[AdtDef]) -> Result<()> {
    let mut adt_names = HashMap::new();
    for adt in adts {
        if adt_names.insert(adt.name.clone(), ()).is_some() {
            bail!("ADT '{}' is defined multiple times", adt.name);
        }
        let mut variant_names = HashMap::new();
        for variant in &adt.variants {
            if variant_names.insert(variant.name.clone(), ()).is_some() {
                bail!(
                    "variant '{}::{}' is defined multiple times",
                    adt.name,
                    variant.name
                );
            }
            for field in &variant.fields {
                validate_type(field, adts)?;
            }
        }
    }
    Ok(())
}

fn validate_type(ty: &Type, adts: &[AdtDef]) -> Result<()> {
    match ty {
        Type::Int => Ok(()),
        Type::Func { params } => {
            for param in params {
                validate_type(param, adts)?;
            }
            Ok(())
        }
        Type::Adt(name) => {
            if adts.iter().any(|adt| &adt.name == name) {
                Ok(())
            } else {
                bail!("unknown ADT type '{}'", name)
            }
        }
        Type::Sender(payload) | Type::Receiver(payload) => validate_type(payload, adts),
    }
}

fn validate_function(func: &Function, ctx: &Ctx<'_>) -> Result<()> {
    let mut env = Env::default();
    for (param_name, param_ty) in &func.params {
        env.declare(param_name.clone(), param_ty.clone())?;
    }
    validate_statement(&func.body, &mut env, ctx)
}

fn validate_init(init: &FuncCall, ctx: &Ctx<'_>) -> Result<()> {
    let mut env = Env::default();
    for var in init.free_vars() {
        env.ensure_external_int(&var);
    }
    validate_tail_call(init, &mut env, ctx)
}

fn validate_statement(stmt: &Statement, env: &mut Env, ctx: &Ctx<'_>) -> Result<()> {
    match stmt {
        Statement::Fail | Statement::Unit => Ok(()),
        Statement::Call(call) => validate_tail_call(call, env, ctx),
        Statement::If(cond, then_call, else_call) => {
            expect_expr_type(cond, &Type::Int, env, ctx)?;
            let mut then_env = env.clone();
            validate_tail_call(then_call, &mut then_env, ctx)?;
            let mut else_env = env.clone();
            validate_tail_call(else_call, &mut else_env, ctx)
        }
        Statement::Spawn(first, second) => {
            validate_call(first, env, ctx)?;
            validate_tail_call(second, env, ctx)
        }
        Statement::New {
            payload,
            sender,
            receiver,
            body,
        } => {
            if sender == receiver {
                bail!("new binds the same variable '{}' twice", sender);
            }
            let mut body_env = env.clone();
            body_env.declare(sender.clone(), Type::sender(payload.clone()))?;
            body_env.declare(receiver.clone(), Type::receiver(payload.clone()))?;
            validate_tail_call(body, &mut body_env, ctx)
        }
        Statement::Send {
            sender,
            value,
            body,
        } => {
            let sender_ty = env.ty_of(sender)?;
            let Type::Sender(payload) = sender_ty else {
                bail!("variable '{}' is not a sender", sender);
            };
            expect_expr_type(value, &payload, env, ctx)?;
            validate_tail_call(body, env, ctx)
        }
        Statement::Recv {
            receiver,
            var,
            body,
        } => {
            let receiver_ty = env.ty_of(receiver)?;
            let Type::Receiver(payload) = receiver_ty else {
                bail!("variable '{}' is not a receiver", receiver);
            };
            let mut body_env = env.clone();
            body_env.declare(var.clone(), *payload)?;
            validate_tail_call(body, &mut body_env, ctx)
        }
        Statement::Dup { sender, var, body } => {
            let sender_ty = env.ty_of(sender)?;
            if !matches!(sender_ty, Type::Sender(_)) {
                bail!("variable '{}' is not a sender", sender);
            }
            let mut body_env = env.clone();
            body_env.declare(var.clone(), sender_ty)?;
            validate_tail_call(body, &mut body_env, ctx)
        }
        Statement::Match { scrutinee, arms } => validate_match(scrutinee, arms, env, ctx),
    }
}

fn validate_match(scrutinee: &str, arms: &[MatchArm], env: &mut Env, ctx: &Ctx<'_>) -> Result<()> {
    let scrutinee_ty = env.ty_of(scrutinee)?;
    let Type::Adt(type_name) = &scrutinee_ty else {
        bail!("variable '{}' is not an ADT", scrutinee);
    };
    validate_match_arms(arms, ctx)?;
    let adt = find_adt(ctx, type_name)?;
    env.consume_if_linear(scrutinee)?;
    let after_scrutinee_env = env.clone();

    for arm in arms {
        if &arm.type_name != type_name {
            bail!(
                "match arm uses ADT '{}', expected '{}'",
                arm.type_name,
                type_name
            );
        }
        let variant = find_variant(adt, &arm.variant)?;
        let mut arm_env = after_scrutinee_env.clone();
        for (var, field_ty) in arm.vars.iter().zip(&variant.fields) {
            arm_env.declare(var.clone(), field_ty.clone())?;
        }
        validate_tail_call(&arm.body, &mut arm_env, ctx)?;
    }
    Ok(())
}

fn validate_match_arms(arms: &[MatchArm], ctx: &Ctx<'_>) -> Result<()> {
    let Some(first_arm) = arms.first() else {
        bail!("match must have at least one arm");
    };
    let adt = find_adt(ctx, &first_arm.type_name)?;
    let mut seen = HashMap::new();
    for arm in arms {
        if arm.type_name != adt.name {
            bail!(
                "match arm uses ADT '{}', expected '{}'",
                arm.type_name,
                adt.name
            );
        }
        let variant = find_variant(adt, &arm.variant)?;
        if seen.insert(arm.variant.clone(), ()).is_some() {
            bail!(
                "match arm for '{}::{}' is defined multiple times",
                arm.type_name,
                arm.variant
            );
        }
        if arm.vars.len() != variant.fields.len() {
            bail!(
                "variant '{}::{}' expects {} fields, got {}",
                arm.type_name,
                arm.variant,
                variant.fields.len(),
                arm.vars.len()
            );
        }
    }
    for variant in &adt.variants {
        if !seen.contains_key(&variant.name) {
            bail!("match is missing arm '{}::{}'", adt.name, variant.name);
        }
    }
    Ok(())
}

fn validate_call(call: &FuncCall, env: &mut Env, ctx: &Ctx<'_>) -> Result<()> {
    let sig = ctx
        .functions
        .get(call.name.as_str())
        .ok_or_else(|| anyhow!("undefined function '{}'", call.name))?;
    if call.args.len() != sig.params.len() {
        bail!(
            "function '{}' expects {} arguments, got {}",
            call.name,
            sig.params.len(),
            call.args.len()
        );
    }
    for (arg, expected_ty) in call.args.iter().zip(&sig.params) {
        expect_expr_type(arg, expected_ty, env, ctx)?;
    }
    Ok(())
}

fn validate_tail_call(call: &FuncCall, env: &mut Env, ctx: &Ctx<'_>) -> Result<()> {
    validate_call(call, env, ctx)?;
    env.ensure_no_unconsumed_linear()
}

fn infer_expr_type(expr: &Expr, env: &mut Env, ctx: &Ctx<'_>) -> Result<Type> {
    match expr {
        Expr::Num(_) => Ok(Type::Int),
        Expr::Var(var) => {
            let ty = env.ty_of(var)?;
            env.consume_if_linear(var)?;
            Ok(ty)
        }
        Expr::Ctor {
            type_name,
            variant,
            args,
        } => {
            let adt = find_adt(ctx, type_name)?;
            let variant_def = find_variant(adt, variant)?;
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
                expect_expr_type(arg, expected_ty, env, ctx)?;
            }
            Ok(Type::Adt(type_name.clone()))
        }
        Expr::Op(lhs, _, rhs) => {
            expect_expr_type(lhs, &Type::Int, env, ctx)?;
            expect_expr_type(rhs, &Type::Int, env, ctx)?;
            Ok(Type::Int)
        }
    }
}

fn expect_expr_type(expr: &Expr, expected: &Type, env: &mut Env, ctx: &Ctx<'_>) -> Result<()> {
    let before = env.clone();
    let actual = infer_expr_type(expr, env, ctx)?;
    if &actual != expected {
        *env = before;
        bail!(
            "expected expression of type {:?}, got {:?}",
            expected,
            actual
        );
    }
    Ok(())
}

fn find_adt<'a>(ctx: &Ctx<'a>, name: &str) -> Result<&'a AdtDef> {
    ctx.adts
        .get(name)
        .copied()
        .ok_or_else(|| anyhow!("unknown ADT type '{}'", name))
}

fn find_variant<'a>(adt: &'a AdtDef, name: &str) -> Result<&'a VariantDef> {
    adt.variants
        .iter()
        .find(|variant| variant.name == name)
        .ok_or_else(|| anyhow!("unknown variant '{}::{}'", adt.name, name))
}

#[cfg(test)]
mod tests {
    use crate::core::parser;

    fn parse_err(input: &str) -> String {
        parser::parse_program(input)
            .expect_err("program should be rejected")
            .to_string()
    }

    #[test]
    fn moves_linear_values_into_adt_constructors() {
        let err = parse_err(
            r#"
            data Box = Hold(Sender<int>)

            init = main()

            main() = new s, r in use_box(Box::Hold(s), s, r)
            use_box(b: Box, s: Sender<int>, r: Receiver<int>) = ()
            "#,
        );

        assert!(err.contains("move"));
    }

    #[test]
    fn rejects_double_use_of_linear_function_argument() {
        let err = parse_err(
            r#"
            init = main()

            main() = new s, r in use_twice(s, s, r)
            use_twice(s1: Sender<int>, s2: Sender<int>, r: Receiver<int>) = ()
            "#,
        );

        assert!(err.contains("move"));
    }

    #[test]
    fn rejects_implicit_drop_before_tail_call() {
        let err = parse_err(
            r#"
            init = main()

            main() = new s, r in done(s)
            done(s: Sender<int>) = ()
            "#,
        );

        assert!(err.contains("not moved before non-terminal control transfer"));
    }

    #[test]
    fn accepts_if_branches_that_move_the_same_linear_value() {
        parser::parse_program(
            r#"
            init = main(n)

            main(n: int) = new s, r in branch(n, s, r)
            branch(n: int, s: Sender<int>, r: Receiver<int>) = if n then left(s, r) else right(s, r)
            left(s: Sender<int>, r: Receiver<int>) = ()
            right(s: Sender<int>, r: Receiver<int>) = ()
            "#,
        )
        .expect("alternative branches may consume the same incoming linear value");
    }

    #[test]
    fn rejects_spawn_using_moved_linear_value_in_second_call() {
        let err = parse_err(
            r#"
            init = main()

            main() = new s, r in do_spawn(s, r)
            do_spawn(s: Sender<int>, r: Receiver<int>) = spawn(first(s)); second(s, r)
            first(s: Sender<int>) = ()
            second(s: Sender<int>, r: Receiver<int>) = ()
            "#,
        );

        assert!(err.contains("move"));
    }

    #[test]
    fn rejects_payload_type_mismatch_in_send() {
        let err = parse_err(
            r#"
            data Box = Hold(int)

            init = main()

            main() = new<Box> s, r in do_send(s, r)
            do_send(s: Sender<Box>, r: Receiver<Box>) = send 1 to s; done(s, r)
            done(s: Sender<Box>, r: Receiver<Box>) = ()
            "#,
        );

        assert!(err.contains("expected expression of type"));
    }

    #[test]
    fn rejects_match_on_non_adt() {
        let err = parse_err(
            r#"
            data Box = Hold(int)

            init = main(0)

            main(n: int) = match n { Box::Hold(v) => done(v) }
            done(v: int) = ()
            "#,
        );

        assert!(err.contains("is not an ADT"));
    }
}

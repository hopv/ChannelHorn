use anyhow::{Result, bail};
use rand;
use std::{
    cell::{Cell, RefCell},
    collections::{HashMap, VecDeque},
    rc::Rc,
};

use super::ast::{Expr, FuncCall, OpKind, Program, Statement, VarName};

#[derive(Debug)]
pub struct Evaluator {
    threads: Vec<Thread>,
    program: Program,
    fresh_num: Cell<usize>,
}

#[derive(Debug)]
pub struct Thread {
    pub statement: Statement,
    pub env: HashMap<VarName, Value>,
}

type Channel = Rc<RefCell<VecDeque<Value>>>;

#[derive(Debug, Clone)]
pub enum Value {
    Int(i32),
    Sender(Channel),
    Receiver(Channel),
    Adt {
        type_name: String,
        variant: String,
        fields: Vec<Value>,
    },
}

impl Evaluator {
    pub fn new(prog: Program) -> Result<Self> {
        let free_vars = prog.init.free_vars();
        let mut env = HashMap::new();
        for var in free_vars {
            println!("Please provide an integer value for variable {}:", var);
            let value = {
                let mut buffer = "".to_string();
                std::io::stdin().read_line(&mut buffer)?;
                buffer.trim().parse::<i32>()?
            };
            println!("Initializing variable {} with value {}", var, value);
            env.insert(var, Value::Int(value));
        }
        let main_thread = Thread {
            statement: Statement::Call(prog.init.clone()),
            env,
        };
        Ok(Evaluator {
            threads: vec![main_thread],
            program: prog,
            fresh_num: Cell::new(0),
        })
    }

    pub fn is_done(&self) -> bool {
        self.threads.is_empty()
    }

    fn fresh_var(fresh_num: &Cell<usize>) -> VarName {
        let num = fresh_num.get();
        fresh_num.set(num + 1);
        format!("%{}", num)
    }

    /// Performs a small step of evaluation.
    /// Returns Err(err) if the program fails.
    pub fn step(&mut self) -> Result<()> {
        if self.threads.is_empty() {
            return Ok(());
        }
        let exec_thread_index = rand::random_range(0..self.threads.len());
        let result: Option<Statement> = self.step_statement(exec_thread_index)?;
        match result {
            Some(new_statement) => {
                self.threads[exec_thread_index].statement = new_statement;
            }
            None => {
                self.threads.remove(exec_thread_index);
            }
        }
        Ok(())
    }

    fn step_statement(&mut self, thread_index: usize) -> Result<Option<Statement>> {
        let thread = &mut self.threads[thread_index];
        let env = &mut thread.env;
        let fun_def = &self.program.functions;
        match &thread.statement {
            Statement::Fail => bail!("Program failed"),
            Statement::Unit => Ok(None),
            Statement::Call(FuncCall { name, args }) => {
                let evaluated_args = args
                    .iter()
                    .map(|arg| arg.step(env))
                    .collect::<Result<Vec<Value>>>()?;
                match fun_def.get(name) {
                    Some(func) => {
                        let mut body = func.body.clone();
                        let var_map = func
                            .params
                            .iter()
                            .map(|(param_var, _)| {
                                (param_var.clone(), Self::fresh_var(&self.fresh_num))
                            })
                            .collect::<HashMap<VarName, VarName>>();
                        body.substitute_var(&var_map);
                        for ((param_var, _), arg_val) in func.params.iter().zip(evaluated_args) {
                            env.insert(var_map.get(param_var).unwrap().clone(), arg_val);
                        }
                        Ok(Some(body))
                    }
                    None => bail!("Undefined function: {:?}", name),
                }
            }
            Statement::If(expr, then_call, else_call) => {
                let cond_value = expr.step(env)?;
                match cond_value {
                    Value::Int(n) => {
                        if n != 0 {
                            Ok(Some(Statement::Call(then_call.clone())))
                        } else {
                            Ok(Some(Statement::Call(else_call.clone())))
                        }
                    }
                    _ => bail!("Condition expression must evaluate to an integer"),
                }
            }
            Statement::Spawn(func_call, func_call1) => {
                let new_thread = Thread {
                    statement: Statement::Call(func_call1.clone()),
                    env: env.clone(),
                };
                let func_call = func_call.clone();
                self.threads.push(new_thread);
                Ok(Some(Statement::Call(func_call)))
            }
            Statement::New {
                payload: _,
                sender,
                receiver,
                body,
            } => {
                let channel: Channel = Rc::new(RefCell::new(VecDeque::new()));
                let new_sender_var = Self::fresh_var(&self.fresh_num);
                let new_receiver_var = Self::fresh_var(&self.fresh_num);
                env.insert(new_sender_var.clone(), Value::Sender(channel.clone()));
                env.insert(new_receiver_var.clone(), Value::Receiver(channel.clone()));
                let mut body = body.clone();
                body.substitute_var(&HashMap::from([
                    (sender.clone(), new_sender_var),
                    (receiver.clone(), new_receiver_var),
                ]));
                Ok(Some(Statement::Call(body)))
            }
            Statement::Send {
                sender,
                value,
                body,
            } => {
                let sender_value = env.get(sender).ok_or_else(|| {
                    anyhow::anyhow!("Undefined variable for sender: {:?}", sender)
                })?;
                let value = value.step(env)?;
                match sender_value {
                    Value::Sender(channel) => {
                        channel.borrow_mut().push_back(value);
                    }
                    _ => bail!("Variable is not a sender: {:?}", sender),
                }
                Ok(Some(Statement::Call(body.clone())))
            }
            Statement::Recv {
                receiver,
                var,
                body,
            } => {
                let receiver_value = env.get(receiver).ok_or_else(|| {
                    anyhow::anyhow!("Undefined variable for receiver: {:?}", receiver)
                })?;
                match receiver_value.clone() {
                    Value::Receiver(channel) => {
                        let mut channel = channel.borrow_mut();
                        if let Some(received_value) = channel.pop_front() {
                            let fresh_var = Self::fresh_var(&self.fresh_num);
                            env.insert(fresh_var.clone(), received_value);
                            let mut body = body.clone();
                            body.substitute_var(&HashMap::from([(var.clone(), fresh_var)]));
                            Ok(Some(Statement::Call(body.clone())))
                        } else {
                            // Channel is empty, cannot proceed
                            Ok(Some(thread.statement.clone()))
                        }
                    }
                    _ => bail!("Variable is not a receiver: {:?}", receiver),
                }
            }
            Statement::Match { scrutinee, arms } => {
                let scrutinee_value = env.get(scrutinee).ok_or_else(|| {
                    anyhow::anyhow!("Undefined variable for match: {:?}", scrutinee)
                })?;
                match scrutinee_value.clone() {
                    Value::Adt {
                        type_name,
                        variant,
                        fields,
                    } => {
                        let arm = arms
                            .iter()
                            .find(|arm| arm.type_name == type_name && arm.variant == variant)
                            .ok_or_else(|| {
                                anyhow::anyhow!("No match arm for {}::{}", type_name, variant)
                            })?;
                        if arm.vars.len() != fields.len() {
                            bail!(
                                "Match arm {}::{} expects {} fields, got {}",
                                type_name,
                                variant,
                                arm.vars.len(),
                                fields.len()
                            );
                        }
                        let mut var_map = HashMap::new();
                        for (var, field) in arm.vars.iter().zip(fields) {
                            let fresh_var = Self::fresh_var(&self.fresh_num);
                            env.insert(fresh_var.clone(), field);
                            var_map.insert(var.clone(), fresh_var);
                        }
                        let mut body = arm.body.clone();
                        body.substitute_var(&var_map);
                        Ok(Some(Statement::Call(body)))
                    }
                    _ => bail!("Variable is not an ADT value: {:?}", scrutinee),
                }
            }
            Statement::Dup { sender, var, body } => {
                let sender_value = env.get(sender).ok_or_else(|| {
                    anyhow::anyhow!("Undefined variable for sender: {:?}", sender)
                })?;
                match sender_value.clone() {
                    Value::Sender(channel) => {
                        let new_sender_var = Self::fresh_var(&self.fresh_num);
                        env.insert(new_sender_var.clone(), Value::Sender(channel.clone()));
                        let mut body = body.clone();
                        body.substitute_var(&HashMap::from([(var.clone(), new_sender_var)]));
                        Ok(Some(Statement::Call(body.clone())))
                    }
                    _ => bail!("Variable is not a sender: {:?}", sender),
                }
            }
        }
    }
}

impl Expr {
    fn step(&self, env: &HashMap<VarName, Value>) -> Result<Value> {
        match self {
            Expr::Num(n) => Ok(Value::Int(*n)),
            Expr::Var(var) => match env.get(var) {
                Some(val) => Ok(val.clone()),
                None => bail!("Undefined variable: {:?}", var),
            },
            Expr::Ctor {
                type_name,
                variant,
                args,
            } => {
                let fields = args
                    .iter()
                    .map(|arg| arg.step(env))
                    .collect::<Result<Vec<_>>>()?;
                Ok(Value::Adt {
                    type_name: type_name.clone(),
                    variant: variant.clone(),
                    fields,
                })
            }
            Expr::Op(expr, op_kind, expr1) => {
                let v1 = expr.step(env)?;
                let v2 = expr1.step(env)?;
                match op_kind {
                    OpKind::Add => {
                        if let (Value::Int(n1), Value::Int(n2)) = (v1, v2) {
                            Ok(Value::Int(n1 + n2))
                        } else {
                            bail!("Type error in addition")
                        }
                    }
                    OpKind::Eq => {
                        if let (Value::Int(n1), Value::Int(n2)) = (v1, v2) {
                            if n1 == n2 {
                                Ok(Value::Int(1))
                            } else {
                                Ok(Value::Int(0))
                            }
                        } else {
                            bail!("Type error in equality check")
                        }
                    }
                    OpKind::Sub => {
                        if let (Value::Int(n1), Value::Int(n2)) = (v1, v2) {
                            Ok(Value::Int(n1 - n2))
                        } else {
                            bail!("Type error in subtraction")
                        }
                    }
                    OpKind::Mul => {
                        if let (Value::Int(n1), Value::Int(n2)) = (v1, v2) {
                            Ok(Value::Int(n1 * n2))
                        } else {
                            bail!("Type error in multiplication")
                        }
                    }
                    OpKind::Ne => {
                        if let (Value::Int(n1), Value::Int(n2)) = (v1, v2) {
                            if n1 != n2 {
                                Ok(Value::Int(1))
                            } else {
                                Ok(Value::Int(0))
                            }
                        } else {
                            bail!("Type error in inequality check")
                        }
                    }
                    OpKind::Lt => {
                        if let (Value::Int(n1), Value::Int(n2)) = (v1, v2) {
                            if n1 < n2 {
                                Ok(Value::Int(1))
                            } else {
                                Ok(Value::Int(0))
                            }
                        } else {
                            bail!("Type error in less-than check")
                        }
                    }
                    OpKind::Le => {
                        if let (Value::Int(n1), Value::Int(n2)) = (v1, v2) {
                            if n1 <= n2 {
                                Ok(Value::Int(1))
                            } else {
                                Ok(Value::Int(0))
                            }
                        } else {
                            bail!("Type error in less-than-or-equal check")
                        }
                    }
                    OpKind::Gt => {
                        if let (Value::Int(n1), Value::Int(n2)) = (v1, v2) {
                            if n1 > n2 {
                                Ok(Value::Int(1))
                            } else {
                                Ok(Value::Int(0))
                            }
                        } else {
                            bail!("Type error in greater-than check")
                        }
                    }
                    OpKind::Ge => {
                        if let (Value::Int(n1), Value::Int(n2)) = (v1, v2) {
                            if n1 >= n2 {
                                Ok(Value::Int(1))
                            } else {
                                Ok(Value::Int(0))
                            }
                        } else {
                            bail!("Type error in greater-than-or-equal check")
                        }
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::parser;

    #[test]
    fn can_send_and_receive_channel_values() {
        let program = parser::parse_program(
            r#"
            init = main()

            main() = new<Sender<int>> s, r in make(s, r)
            make(s: Sender<Sender<int>>, r: Receiver<Sender<int>>) = new is, ir in send_inner(s, r, is, ir)
            send_inner(s: Sender<Sender<int>>, r: Receiver<Sender<int>>, is: Sender, ir: Receiver) = send is to s; use_received_sender(s, r, ir)
            use_received_sender(s: Sender<Sender<int>>, r: Receiver<Sender<int>>, ir: Receiver<int>) = let received_s = recv r in send_on_received(received_s, s, r, ir)
            send_on_received(received_s: Sender, s: Sender<Sender<int>>, r: Receiver<Sender<int>>, ir: Receiver<int>) = send 1 to received_s; read_int(received_s, s, r, ir)
            read_int(received_s: Sender, s: Sender<Sender<int>>, r: Receiver<Sender<int>>, ir: Receiver) = let x = recv ir in check_int(x, received_s, s, r, ir)
            check_int(x: int, received_s: Sender, s: Sender<Sender<int>>, r: Receiver<Sender<int>>, ir: Receiver<int>) = if x == 1 then unit(received_s, s, r, ir) else fail(received_s, s, r, ir)
            unit(received_s: Sender, s: Sender<Sender<int>>, r: Receiver<Sender<int>>, ir: Receiver<int>) = ()
            fail(received_s: Sender, s: Sender<Sender<int>>, r: Receiver<Sender<int>>, ir: Receiver<int>) = fail
            "#,
        )
        .expect("program should parse");
        let mut evaluator = Evaluator::new(program).expect("evaluator should initialize");

        for _ in 0..100 {
            if evaluator.is_done() {
                return;
            }
            evaluator.step().expect("evaluation should not fail");
        }

        panic!("evaluation did not finish");
    }

    #[test]
    fn can_match_adt_values() {
        let program = parser::parse_program(
            r#"
            data Option = None | Some(int)

            init = main()

            main() = use(Option::Some(1))
            use(opt: Option) = match opt {
                Option::None() => fail(),
                Option::Some(v) => check(v),
            }
            check(v: int) = if v == 1 then unit() else fail()
            unit() = ()
            fail() = fail
            "#,
        )
        .expect("program should parse");
        let mut evaluator = Evaluator::new(program).expect("evaluator should initialize");

        for _ in 0..20 {
            if evaluator.is_done() {
                return;
            }
            evaluator.step().expect("evaluation should not fail");
        }

        panic!("evaluation did not finish");
    }
}

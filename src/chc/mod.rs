use std::collections::HashMap;

use crate::core::ast::VarName;

pub mod display;

pub type PredicateName = String;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PredicateAtom {
    pub name: PredicateName,
    pub args: Vec<Term>,
}

impl PredicateAtom {
    pub fn substitute(&mut self, var_map: &HashMap<VarName, VarName>) {
        for arg in &mut self.args {
            arg.substitute(var_map);
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    Var(VarName),
    Int(i32),
    Ctor { name: String, args: Vec<Term> },
    Add(Box<Term>, Box<Term>),
    Sub(Box<Term>, Box<Term>),
    Mul(Box<Term>, Box<Term>),
    Bool(bool),
    LOr(Box<Term>, Box<Term>),
    Eq(Box<Term>, Box<Term>),
    Ne(Box<Term>, Box<Term>),
    Lt(Box<Term>, Box<Term>),
    Le(Box<Term>, Box<Term>),
    Gt(Box<Term>, Box<Term>),
    Ge(Box<Term>, Box<Term>),
    Cons(Box<Term>, Box<Term>),
    Nil(Type),
    Head(Box<Term>),
    Tail(Box<Term>),
    Pair(Box<Term>, Box<Term>),
    Key(Box<Term>),
    Val(Box<Term>),
}

impl Term {
    pub fn substitute(&mut self, var_map: &HashMap<VarName, VarName>) {
        match self {
            Term::Var(v) => {
                if let Some(new_v) = var_map.get(v) {
                    *v = new_v.clone();
                }
            }
            Term::Ctor { args, .. } => {
                for arg in args {
                    arg.substitute(var_map);
                }
            }
            Term::Add(lhs, rhs)
            | Term::Sub(lhs, rhs)
            | Term::Mul(lhs, rhs)
            | Term::LOr(lhs, rhs)
            | Term::Eq(lhs, rhs)
            | Term::Ne(lhs, rhs)
            | Term::Lt(lhs, rhs)
            | Term::Le(lhs, rhs)
            | Term::Gt(lhs, rhs)
            | Term::Ge(lhs, rhs)
            | Term::Pair(lhs, rhs)
            | Term::Cons(lhs, rhs) => {
                lhs.substitute(var_map);
                rhs.substitute(var_map);
            }
            Term::Head(t) | Term::Tail(t) | Term::Key(t) | Term::Val(t) => {
                t.substitute(var_map);
            }
            Term::Int(_) | Term::Bool(_) | Term::Nil(_) => {}
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Constraint {
    Eq(Term, Term),
    Ne(Term, Term),
    Lt(Term, Term),
    Le(Term, Term),
}

impl Constraint {
    pub fn substitute(&mut self, var_map: &HashMap<VarName, VarName>) {
        match self {
            Constraint::Eq(t1, t2)
            | Constraint::Ne(t1, t2)
            | Constraint::Lt(t1, t2)
            | Constraint::Le(t1, t2) => {
                t1.substitute(var_map);
                t2.substitute(var_map);
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Int,
    Bool,
    Adt(String),
    Lst(Box<Type>),
    Pair(Box<Type>, Box<Type>),
    Func { args: Vec<Type> },
}

impl Type {
    pub fn prophecy(no_timestamps: bool, ty: Type) -> Self {
        if no_timestamps {
            Type::Lst(Box::new(ty))
        } else {
            Type::Lst(Box::new(Type::timestamped_value(ty)))
        }
    }

    pub fn timestamped_value(ty: Type) -> Self {
        Type::Pair(Box::new(Type::Int), Box::new(ty))
    }

    fn predicate_suffix(&self) -> String {
        match self {
            Type::Int => "Int".to_string(),
            Type::Bool => "Bool".to_string(),
            Type::Adt(name) => name.clone(),
            Type::Lst(inner) => format!("Lst_{}", inner.predicate_suffix()),
            Type::Pair(first, second) => {
                format!(
                    "Pair_{}_{}",
                    first.predicate_suffix(),
                    second.predicate_suffix()
                )
            }
            Type::Func { args } => {
                let args = args
                    .iter()
                    .map(Type::predicate_suffix)
                    .collect::<Vec<_>>()
                    .join("_");
                format!("Func_{}", args)
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Clause {
    pub forall: Vec<(VarName, Type)>,
    // None represents an implicit false head
    pub head: Option<PredicateAtom>,
    pub body: Body,
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct Body {
    pub predicates: Vec<PredicateAtom>,
    pub constraints: Vec<Constraint>,
}

impl Body {
    pub fn substitute(&mut self, var_map: &HashMap<VarName, VarName>) {
        for pred in &mut self.predicates {
            pred.substitute(var_map);
        }
        for cons in &mut self.constraints {
            cons.substitute(var_map);
        }
    }
}

pub type DisjunctiveBody = Vec<Body>;

impl Body {
    pub fn concat(mut self, other: Body) -> Self {
        self.predicates.extend(other.predicates);
        self.constraints.extend(other.constraints);
        self
    }
}

#[derive(Debug, Default, Clone)]
pub struct Setting {
    pub no_timestamps: bool,
}

#[derive(Debug, Clone)]
pub struct CHC {
    pub clauses: Vec<Clause>,
    pub fun_declarations: HashMap<PredicateName, Vec<Type>>,
    pub datatypes: Vec<Datatype>,
    pub setting: Setting,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Datatype {
    pub name: String,
    pub variants: Vec<DatatypeVariant>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DatatypeVariant {
    pub name: String,
    pub fields: Vec<(String, Type)>,
}

pub static SORTED_PREDICATE: &str = "%Sorted";

pub static MERGE_PREDICATE: &str = "%Merge";

impl CHC {
    pub fn init_premitive(setting: &Setting) -> Self {
        CHC {
            clauses: vec![],
            fun_declarations: HashMap::new(),
            datatypes: vec![],
            setting: setting.clone(),
        }
    }

    pub fn primitive_predicate_names(payload_ty: &Type) -> (PredicateName, PredicateName) {
        if payload_ty == &Type::Int {
            (SORTED_PREDICATE.to_string(), MERGE_PREDICATE.to_string())
        } else {
            let suffix = payload_ty.predicate_suffix();
            (
                format!("{}${}", SORTED_PREDICATE, suffix),
                format!("{}${}", MERGE_PREDICATE, suffix),
            )
        }
    }

    pub fn primitive_fun_declarations(
        setting: &Setting,
        payload_ty: Type,
    ) -> HashMap<PredicateName, Vec<Type>> {
        let prophecy_ty = Type::prophecy(setting.no_timestamps, payload_ty.clone());
        let (sorted_predicate, merge_predicate) = Self::primitive_predicate_names(&payload_ty);
        HashMap::from([
            (sorted_predicate, vec![prophecy_ty.clone()]),
            (
                merge_predicate,
                vec![
                    prophecy_ty.clone(),
                    prophecy_ty.clone(),
                    prophecy_ty.clone(),
                ],
            ),
        ])
    }

    pub fn primitive_clauses(setting: &Setting, payload_ty: Type) -> Vec<Clause> {
        let prophecy_ty = Type::prophecy(setting.no_timestamps, payload_ty.clone());
        let timestamped_value_ty = Type::timestamped_value(payload_ty.clone());
        let (sorted_predicate, merge_predicate) = Self::primitive_predicate_names(&payload_ty);
        let mut clauses = vec![];

        if !setting.no_timestamps {
            let sorted = vec![
                Clause {
                    forall: vec![],
                    head: Some(PredicateAtom {
                        name: sorted_predicate.clone(),
                        args: vec![Term::Nil(prophecy_ty.clone())],
                    }),
                    body: Body {
                        predicates: vec![],
                        constraints: vec![],
                    },
                },
                Clause {
                    forall: vec![
                        ("l".to_string(), prophecy_ty.clone()),
                        ("p".to_string(), timestamped_value_ty.clone()),
                    ],
                    head: Some(PredicateAtom {
                        name: sorted_predicate.clone(),
                        args: vec![Term::Var("l".to_string())],
                    }),
                    body: Body {
                        predicates: vec![],
                        constraints: vec![Constraint::Eq(
                            Term::Var("l".to_string()),
                            Term::Cons(
                                Term::Var("p".to_string()).into(),
                                Term::Nil(prophecy_ty.clone()).into(),
                            ),
                        )],
                    },
                },
                Clause {
                    forall: vec![
                        ("l".to_string(), prophecy_ty.clone()),
                        ("l2".to_string(), prophecy_ty.clone()),
                        ("l3".to_string(), prophecy_ty.clone()),
                        ("p".to_string(), timestamped_value_ty.clone()),
                        ("p2".to_string(), timestamped_value_ty.clone()),
                    ],
                    head: Some(PredicateAtom {
                        name: sorted_predicate.clone(),
                        args: vec![Term::Var("l".to_string())],
                    }),
                    body: Body {
                        predicates: vec![PredicateAtom {
                            name: sorted_predicate,
                            args: vec![Term::Var("l2".to_string())],
                        }],
                        constraints: vec![
                            Constraint::Eq(
                                Term::Var("l".to_string()),
                                Term::Cons(
                                    Term::Var("p".to_string()).into(),
                                    Term::Var("l2".to_string()).into(),
                                ),
                            ),
                            Constraint::Eq(
                                Term::Var("l2".to_string()),
                                Term::Cons(
                                    Term::Var("p2".to_string()).into(),
                                    Term::Var("l3".to_string()).into(),
                                ),
                            ),
                            Constraint::Le(
                                Term::Key(Term::Var("p".to_string()).into()),
                                Term::Key(Term::Var("p2".to_string()).into()),
                            ),
                        ],
                    },
                },
            ];

            clauses.extend(sorted);
        }

        // Merge predicate
        let merge = vec![
            Clause {
                forall: vec![("l".to_string(), prophecy_ty.clone())],
                head: Some(PredicateAtom {
                    name: merge_predicate.clone(),
                    args: vec![
                        Term::Var("l".to_string()),
                        Term::Nil(prophecy_ty.clone()),
                        Term::Var("l".to_string()),
                    ],
                }),
                body: Body::default(),
            },
            Clause {
                forall: vec![("l".to_string(), prophecy_ty.clone())],
                head: Some(PredicateAtom {
                    name: merge_predicate.clone(),
                    args: vec![
                        Term::Nil(prophecy_ty.clone()),
                        Term::Var("l".to_string()),
                        Term::Var("l".to_string()),
                    ],
                }),
                body: Body::default(),
            },
            Clause {
                forall: vec![
                    ("l1".to_string(), prophecy_ty.clone()),
                    ("l2".to_string(), prophecy_ty.clone()),
                    ("l3".to_string(), prophecy_ty.clone()),
                    ("l1tail".to_string(), prophecy_ty.clone()),
                    ("l3tail".to_string(), prophecy_ty.clone()),
                    (
                        "p".to_string(),
                        if setting.no_timestamps {
                            payload_ty.clone()
                        } else {
                            timestamped_value_ty.clone()
                        },
                    ),
                ],
                head: Some(PredicateAtom {
                    name: merge_predicate.clone(),
                    args: vec![
                        Term::Var("l1".to_string()),
                        Term::Var("l2".to_string()),
                        Term::Var("l3".to_string()),
                    ],
                }),
                body: Body {
                    predicates: vec![PredicateAtom {
                        name: merge_predicate.clone(),
                        args: vec![
                            Term::Var("l1tail".to_string()),
                            Term::Var("l2".to_string()),
                            Term::Var("l3tail".to_string()),
                        ],
                    }],
                    constraints: vec![
                        Constraint::Eq(
                            Term::Var("l1".to_string()),
                            Term::Cons(
                                Term::Var("p".to_string()).into(),
                                Term::Var("l1tail".to_string()).into(),
                            ),
                        ),
                        Constraint::Eq(
                            Term::Var("l3".to_string()),
                            Term::Cons(
                                Term::Var("p".to_string()).into(),
                                Term::Var("l3tail".to_string()).into(),
                            ),
                        ),
                    ],
                },
            },
            Clause {
                forall: vec![
                    ("l1".to_string(), prophecy_ty.clone()),
                    ("l2".to_string(), prophecy_ty.clone()),
                    ("l3".to_string(), prophecy_ty.clone()),
                    ("l2tail".to_string(), prophecy_ty.clone()),
                    ("l3tail".to_string(), prophecy_ty.clone()),
                    (
                        "p".to_string(),
                        if setting.no_timestamps {
                            payload_ty.clone()
                        } else {
                            timestamped_value_ty.clone()
                        },
                    ),
                ],
                head: Some(PredicateAtom {
                    name: merge_predicate.clone(),
                    args: vec![
                        Term::Var("l1".to_string()),
                        Term::Var("l2".to_string()),
                        Term::Var("l3".to_string()),
                    ],
                }),
                body: Body {
                    predicates: vec![PredicateAtom {
                        name: merge_predicate,
                        args: vec![
                            Term::Var("l1".to_string()),
                            Term::Var("l2tail".to_string()),
                            Term::Var("l3tail".to_string()),
                        ],
                    }],
                    constraints: vec![
                        Constraint::Eq(
                            Term::Var("l2".to_string()),
                            Term::Cons(
                                Term::Var("p".to_string()).into(),
                                Term::Var("l2tail".to_string()).into(),
                            ),
                        ),
                        Constraint::Eq(
                            Term::Var("l3".to_string()),
                            Term::Cons(
                                Term::Var("p".to_string()).into(),
                                Term::Var("l3tail".to_string()).into(),
                            ),
                        ),
                    ],
                },
            },
        ];

        clauses.extend(merge);

        clauses
    }
}

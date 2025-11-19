use std::collections::HashMap;

use crate::ast::VarName;

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
    Add(Box<Term>, Box<Term>),
    Bool(bool),
    LOr(Box<Term>, Box<Term>),
    Eq(Box<Term>, Box<Term>),
    Cons(Box<Term>, Box<Term>),
    Nil,
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
            Term::Add(lhs, rhs)
            | Term::LOr(lhs, rhs)
            | Term::Eq(lhs, rhs)
            | Term::Pair(lhs, rhs)
            | Term::Cons(lhs, rhs) => {
                lhs.substitute(var_map);
                rhs.substitute(var_map);
            }
            Term::Head(t) | Term::Tail(t) | Term::Key(t) | Term::Val(t) => {
                t.substitute(var_map);
            }
            Term::Int(_) | Term::Bool(_) | Term::Nil => {}
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Int,
    Bool,
    List,
    Pair,
    Func { args: Vec<Type> },
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CHC {
    pub clauses: Vec<Clause>,
    pub fun_declarations: HashMap<PredicateName, Vec<Type>>,
}

pub static SORTED_PREDICATE: &str = "%Sorted";

pub static MERGE_PREDICATE: &str = "%Merge";

impl CHC {
    pub fn init_premitive() -> Self {
        let mut fun_declarations = HashMap::new();
        fun_declarations.insert(SORTED_PREDICATE.to_string(), vec![Type::List]);
        fun_declarations.insert(
            MERGE_PREDICATE.to_string(),
            vec![Type::List, Type::List, Type::List],
        );
        let mut clauses = vec![];
        let sorted = vec![
            Clause {
                forall: vec![],
                head: Some(PredicateAtom {
                    name: SORTED_PREDICATE.to_string(),
                    args: vec![Term::Nil],
                }),
                body: Body {
                    predicates: vec![],
                    constraints: vec![],
                },
            },
            Clause {
                forall: vec![("l".to_string(), Type::List), ("p".to_string(), Type::Pair)],
                head: Some(PredicateAtom {
                    name: SORTED_PREDICATE.to_string(),
                    args: vec![Term::Var("l".to_string())],
                }),
                body: Body {
                    predicates: vec![],
                    constraints: vec![Constraint::Eq(
                        Term::Var("l".to_string()),
                        Term::Cons(Term::Var("p".to_string()).into(), Term::Nil.into()),
                    )],
                },
            },
            Clause {
                forall: vec![
                    ("l".to_string(), Type::List),
                    ("l2".to_string(), Type::List),
                    ("l3".to_string(), Type::List),
                    ("p".to_string(), Type::Pair),
                    ("p2".to_string(), Type::Pair),
                ],
                head: Some(PredicateAtom {
                    name: SORTED_PREDICATE.to_string(),
                    args: vec![Term::Var("l".to_string())],
                }),
                body: Body {
                    predicates: vec![PredicateAtom {
                        name: SORTED_PREDICATE.to_string(),
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

        // Merge predicate
        let merge = vec![
            Clause {
                forall: vec![("l".to_string(), Type::List)],
                head: Some(PredicateAtom {
                    name: MERGE_PREDICATE.to_string(),
                    args: vec![
                        Term::Var("l".to_string()),
                        Term::Nil,
                        Term::Var("l".to_string()),
                    ],
                }),
                body: Body::default(),
            },
            Clause {
                forall: vec![("l".to_string(), Type::List)],
                head: Some(PredicateAtom {
                    name: MERGE_PREDICATE.to_string(),
                    args: vec![
                        Term::Nil,
                        Term::Var("l".to_string()),
                        Term::Var("l".to_string()),
                    ],
                }),
                body: Body::default(),
            },
            Clause {
                forall: vec![
                    ("l1".to_string(), Type::List),
                    ("l2".to_string(), Type::List),
                    ("l3".to_string(), Type::List),
                    ("l1tail".to_string(), Type::List),
                    ("l3tail".to_string(), Type::List),
                    ("p".to_string(), Type::Pair),
                ],
                head: Some(PredicateAtom {
                    name: MERGE_PREDICATE.to_string(),
                    args: vec![
                        Term::Var("l1".to_string()),
                        Term::Var("l2".to_string()),
                        Term::Var("l3".to_string()),
                    ],
                }),
                body: Body {
                    predicates: vec![PredicateAtom {
                        name: MERGE_PREDICATE.to_string(),
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
                    ("l1".to_string(), Type::List),
                    ("l2".to_string(), Type::List),
                    ("l3".to_string(), Type::List),
                    ("l2tail".to_string(), Type::List),
                    ("l3tail".to_string(), Type::List),
                    ("p".to_string(), Type::Pair),
                ],
                head: Some(PredicateAtom {
                    name: MERGE_PREDICATE.to_string(),
                    args: vec![
                        Term::Var("l1".to_string()),
                        Term::Var("l2".to_string()),
                        Term::Var("l3".to_string()),
                    ],
                }),
                body: Body {
                    predicates: vec![PredicateAtom {
                        name: MERGE_PREDICATE.to_string(),
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

        CHC {
            clauses,
            fun_declarations,
        }
    }
}

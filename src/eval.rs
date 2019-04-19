// Copyright (c) 2019 Timo Savola. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

use std::any::Any;
use std::collections::HashMap;
use std::num::ParseIntError;
use std::rc::Rc;
use std::result::Result;

use super::parse::parse_stmt;
use super::parse::Expr;
use super::parse::Pair;

static UNDERSCORE: Expr = Expr::Atom("_");

/// Ref is a native object stored in an Rc<dyn Any>.
pub struct Ref {
    name: &'static str,
    form: bool, // Internal form or extension function?
}

impl ToString for Ref {
    fn to_string(&self) -> String {
        let mut s = String::with_capacity(self.name.len() + 11);
        s.push_str("<function ");
        s.push_str(self.name);
        s.push('>');
        return s;
    }
}

struct Form {
    value: Rc<dyn Any>,
    f: fn(&Expr, &mut Frame) -> Option<Rc<dyn Any>>,
}

/// Fun is an extension function object.
pub trait Fun {
    fn invoke(&self, args: Vec<Rc<dyn Any>>) -> Option<Rc<dyn Any>>;
}

/// FunMut is an extension function object with side-effects.
pub trait FunMut {
    fn invoke(&mut self, args: Vec<Rc<dyn Any>>) -> Option<Rc<dyn Any>>;
}

struct ExtFun<'f> {
    value: Rc<dyn Any>,
    fun: Option<&'f Fun>,
    fun_mut: Option<&'f mut FunMut>,
}

pub struct Env<'f> {
    forms: HashMap<&'static str, Form>,
    exts: HashMap<&'static str, ExtFun<'f>>,
}

impl<'f> Env<'f> {
    pub fn new() -> Self {
        let mut env = Env {
            forms: HashMap::new(),
            exts: HashMap::new(),
        };

        env.forms.insert(
            "and",
            Form {
                value: Rc::new(Ref {
                    name: "and",
                    form: true,
                }),
                f: eval_and,
            },
        );

        env.forms.insert(
            "or",
            Form {
                value: Rc::new(Ref {
                    name: "or",
                    form: true,
                }),
                f: eval_or,
            },
        );

        env
    }

    pub fn register(&mut self, name: &'static str, f: &'f Fun) {
        self.exts.insert(
            name,
            ExtFun {
                value: Rc::new(Ref {
                    name: name,
                    form: false,
                }),
                fun: Some(f),
                fun_mut: None,
            },
        );
    }

    pub fn register_mut(&mut self, name: &'static str, f: &'f mut FunMut) {
        self.exts.insert(
            name,
            ExtFun {
                value: Rc::new(Ref {
                    name: name,
                    form: false,
                }),
                fun: None,
                fun_mut: Some(f),
            },
        );
    }
}

#[derive(Clone)]
pub struct State {
    inner: Rc<StateLayer>,
    pub result_name: String,
    pub result_value: Rc<dyn Any>,
}

impl State {
    pub fn new() -> Self {
        let nil = Rc::new(());

        State {
            inner: Rc::new(StateLayer {
                parent: None,
                name: "_".to_string(),
                value: nil.clone(),
            }),
            result_name: "".to_string(),
            result_value: nil,
        }
    }
}

struct StateLayer {
    parent: Option<Rc<StateLayer>>,
    name: String,
    value: Rc<dyn Any>,
}

struct Frame<'m, 'f> {
    env: &'m mut Env<'f>,
    state: Rc<StateLayer>,
}

/// Parse and evaluate a statement.  A derived state with the result value is
/// returned.
pub fn eval_stmt<'m>(s: &str, state: State, env: &'m mut Env) -> Option<State> {
    if s.trim().len() == 0 {
        return Some(State {
            inner: state.inner,
            result_name: "".to_string(),
            result_value: Rc::new(()),
        });
    }

    if let Some(ref expr) = parse_stmt(s) {
        let mut frame = Frame {
            env: env,
            state: state.inner.clone(),
        };

        let mut expr = expr;
        let mut name = "_".to_string();

        if let Expr::Pair(p) = expr {
            if let Expr::Atom(s) = p.0 {
                if s.starts_with("!") {
                    if s.len() == 1 {
                        name = choose_name(&frame);
                    } else {
                        name = s[1..].to_string();
                    }

                    match p.1 {
                        Expr::Pair(_) => {
                            expr = &p.1;
                        }
                        Expr::Atom(_) => {
                            return None;
                        }
                        Expr::Nil => {
                            expr = &UNDERSCORE;
                        }
                    }
                }
            }
        }

        if let Some(value) = eval_stmt_expr(&expr, &mut frame, !s.trim_start().starts_with("(")) {
            let mut new = Rc::new(StateLayer {
                parent: state.inner.parent.clone(), // Skip innermost layer with old _ value.
                name: name.to_string(),
                value: value.clone(),
            });

            if name != "_" {
                // Bubble old _ value up to innermost new layer.
                new = Rc::new(StateLayer {
                    parent: Some(new),
                    name: "_".to_string(),
                    value: state.inner.value.clone(),
                });
            }

            return Some(State {
                inner: new,
                result_name: name.to_string(),
                result_value: value.clone(),
            });
        }
    }

    None
}

fn eval_stmt_expr(expr: &Expr, frame: &mut Frame, stmt: bool) -> Option<Rc<dyn Any>> {
    match expr {
        Expr::Pair(p) => eval_call(&p, frame, stmt),
        Expr::Atom(s) => eval_atom(s, frame),
        Expr::Nil => Some(Rc::new(())),
    }
}

fn eval_expr(expr: &Expr, frame: &mut Frame) -> Option<Rc<dyn Any>> {
    eval_stmt_expr(expr, frame, false)
}

fn eval_atom(s: &str, frame: &mut Frame) -> Option<Rc<dyn Any>> {
    if s == "true" {
        return Some(Rc::new(true));
    }
    if s == "false" {
        return Some(Rc::new(false));
    }

    if let Some(c) = s.chars().nth(0) {
        if c == '-' {
            if let Some(c) = s.chars().nth(1) {
                if c >= '0' && c <= '9' {
                    eval_number(s)
                } else {
                    eval_symbol(s, frame)
                }
            } else {
                eval_symbol(s, frame)
            }
        } else if c == '"' {
            eval_string(s)
        } else if c >= '0' && c <= '9' {
            eval_number(s)
        } else {
            eval_symbol(s, frame)
        }
    } else {
        None
    }
}

fn eval_number(s: &str) -> Option<Rc<dyn Any>> {
    let r: Result<i64, ParseIntError> = s.parse();
    if let Result::Ok(n) = r {
        return Some(Rc::new(n));
    }

    None
}

fn eval_string(s: &str) -> Option<Rc<dyn Any>> {
    if s.len() < 2 {
        return None;
    }

    let s = &s[1..s.len() - 1];
    let mut buf = String::with_capacity(s.len());
    let mut escape = false;

    for c in s.chars() {
        if escape {
            match c {
                't' => buf.push('\t'),
                'n' => buf.push('\n'),
                'r' => buf.push('\r'),
                _ => buf.push(c),
            }

            escape = false;
        } else if c == '\\' {
            escape = true;
        } else {
            buf.push(c);
        }
    }

    Some(Rc::new(buf))
}

fn eval_symbol<'m, 'f>(s: &str, frame: &Frame<'m, 'f>) -> Option<Rc<dyn Any>> {
    let mut state = &frame.state;

    loop {
        if state.name == s {
            return Some(state.value.clone());
        }

        if let Some(ref parent) = state.parent {
            state = parent;
        } else {
            break;
        }
    }

    if let Some(x) = frame.env.exts.get(s) {
        return Some(x.value.clone());
    }

    if let Some(x) = frame.env.forms.get(s) {
        return Some(x.value.clone());
    }

    None
}

fn eval_call(p: &Pair, frame: &mut Frame, stmt: bool) -> Option<Rc<dyn Any>> {
    if let Some(x) = eval_expr(&p.0, frame) {
        if let Some(fnref) = x.downcast_ref::<Ref>() {
            if fnref.form {
                return (frame.env.forms.get(fnref.name).unwrap().f)(&p.1, frame);
            } else {
                let mut args = Vec::new();
                if eval_args(&mut args, &p.1, frame) {
                    if let Some(ext) = frame.env.exts.get_mut(fnref.name) {
                        if let Some(fun) = ext.fun {
                            return fun.invoke(args);
                        } else if let Some(ref mut fun) = ext.fun_mut {
                            return fun.invoke(args);
                        }
                    }
                }
            }
        }

        if stmt {
            if let Expr::Nil = p.1 {
                return Some(x);
            }
        }
    }

    None
}

fn eval_and(args: &Expr, frame: &mut Frame) -> Option<Rc<dyn Any>> {
    match args {
        Expr::Pair(p) => {
            if let Some(x) = eval_expr(&p.0, frame) {
                if is_truthful(x.clone()) {
                    if let Expr::Nil = p.1 {
                        Some(x) // Final argument.
                    } else {
                        eval_and(&p.1, frame)
                    }
                } else {
                    Some(x)
                }
            } else {
                None
            }
        }
        Expr::Atom(_) => None,
        Expr::Nil => Some(Rc::new(true)),
    }
}

fn eval_or(args: &Expr, frame: &mut Frame) -> Option<Rc<dyn Any>> {
    match args {
        Expr::Pair(p) => {
            if let Some(x) = eval_expr(&p.0, frame) {
                if is_truthful(x.clone()) {
                    Some(x)
                } else {
                    if let Expr::Nil = p.1 {
                        Some(x) // Final argument.
                    } else {
                        eval_or(&p.1, frame)
                    }
                }
            } else {
                None
            }
        }
        Expr::Atom(_) => None,
        Expr::Nil => Some(Rc::new(false)),
    }
}

fn eval_args(dest: &mut Vec<Rc<dyn Any>>, args: &Expr, frame: &mut Frame) -> bool {
    match args {
        Expr::Pair(p) => {
            if let Some(x) = eval_expr(&p.0, frame) {
                dest.push(x);
                eval_args(dest, &p.1, frame)
            } else {
                false
            }
        }
        Expr::Atom(_) => false,
        Expr::Nil => true,
    }
}

pub fn is_truthful(x: Rc<dyn Any>) -> bool {
    if let Some(_) = x.downcast_ref::<()>() {
        return false;
    }

    if let Some(b) = x.downcast_ref::<bool>() {
        return *b;
    }

    if let Some(n) = x.downcast_ref::<i64>() {
        return *n != 0;
    }

    if let Some(s) = x.downcast_ref::<String>() {
        return !s.is_empty();
    }

    true
}

fn choose_name<'m, 'f>(frame: &Frame<'m, 'f>) -> String {
    for i in 1.. {
        let s = format!("${}", i);
        if let Some(_) = eval_symbol(&s, frame) {
            continue;
        }
        return s;
    }

    panic!();
}

#[cfg(test)]
mod tests {
    use super::*;

    fn eval<'m>(s: &str, env: &'m mut Env) -> Rc<dyn Any> {
        eval_stmt(s, State::new(), env)
            .unwrap()
            .result_value
            .clone()
    }

    struct Id;

    impl Fun for Id {
        fn invoke(&self, args: Vec<Rc<dyn Any>>) -> Option<Rc<dyn Any>> {
            if args.len() == 1 {
                Some(args[0].clone())
            } else {
                None
            }
        }
    }

    struct Greet {
        greetings: i32,
    }

    impl FunMut for Greet {
        fn invoke(&mut self, args: Vec<Rc<dyn Any>>) -> Option<Rc<dyn Any>> {
            if let Some(x) = args.first() {
                if let Some(b) = x.downcast_ref::<bool>() {
                    if *b {
                        self.greetings += 1;
                        return Some(Rc::new("hello, world".to_string()));
                    }
                }
            }

            Some(Rc::new(()))
        }
    }

    #[test]
    fn test_eval_stmt() {
        let id = Id {};
        let mut greet1 = Greet { greetings: 0 };
        let mut greet2 = Greet { greetings: 0 };
        let mut e = Env::new();
        e.register("id", &id);
        e.register_mut("greet-1", &mut greet1);
        e.register_mut("greet-2", &mut greet2);

        assert_eq!(*eval("id 123", &mut e).downcast_ref::<i64>().unwrap(), 123);

        assert_eq!(
            *eval("(greet-1 true)", &mut e)
                .downcast_ref::<String>()
                .unwrap(),
            "hello, world"
        );

        assert_eq!(
            *eval("id (id -123)", &mut e).downcast_ref::<i64>().unwrap(),
            -123
        );

        eval("(greet-2 true)", &mut e);
        eval("(greet-2 true)", &mut e);
        eval("(greet-2 false)", &mut e);
        assert_eq!(greet1.greetings, 1);
        assert_eq!(greet2.greetings, 2);
    }

    #[test]
    fn test_eval_string() {
        let id = Id {};
        let mut e = Env::new();
        e.register("id", &id);

        assert_eq!(
            *eval(r#"id "foo""#, &mut e)
                .downcast_ref::<String>()
                .unwrap(),
            "foo"
        );

        assert_eq!(
            *eval(r#"id "foo\n""#, &mut e)
                .downcast_ref::<String>()
                .unwrap(),
            "foo\n"
        );

        assert_eq!(
            *eval(r#"id "\"foo\"""#, &mut e)
                .downcast_ref::<String>()
                .unwrap(),
            r#""foo""#
        );
    }

    #[test]
    fn test_forms() {
        let mut e = Env::new();

        assert_eq!(*eval("(and)", &mut e).downcast_ref::<bool>().unwrap(), true);
        assert_eq!(
            *eval("(and (and true true) true)", &mut e)
                .downcast_ref::<bool>()
                .unwrap(),
            true
        );
        assert_eq!(
            *eval("(and (and (and (and)) (and)) (and false))", &mut e)
                .downcast_ref::<bool>()
                .unwrap(),
            false
        );

        assert_eq!(*eval("(or)", &mut e).downcast_ref::<bool>().unwrap(), false);
        assert_eq!(
            *eval("(or (or false false) true)", &mut e)
                .downcast_ref::<bool>()
                .unwrap(),
            true
        );
        assert_eq!(
            *eval("(or (or (or (or)) (or)) (or false))", &mut e)
                .downcast_ref::<bool>()
                .unwrap(),
            false
        );
    }

    #[test]
    fn test_state() {
        let id = Id {};
        let mut e = Env::new();
        e.register("id", &id);

        let s = State::new();

        let s = eval_stmt("!x id true", s, &mut e).unwrap();
        let s = eval_stmt("id x", s, &mut e).unwrap();
        assert_eq!(s.result_value.downcast_ref::<bool>().unwrap().clone(), true);
        let s = eval_stmt("id _", s, &mut e).unwrap();
        assert_eq!(s.result_value.downcast_ref::<bool>().unwrap().clone(), true);

        let s = eval_stmt("id 123", s, &mut e).unwrap();
        let s = eval_stmt("id _", s, &mut e).unwrap();
        assert_eq!(s.result_value.downcast_ref::<i64>().unwrap().clone(), 123);
        let s = eval_stmt("!y", s, &mut e).unwrap();
        let s = eval_stmt("id y", s, &mut e).unwrap();
        assert_eq!(s.result_value.downcast_ref::<i64>().unwrap().clone(), 123);

        let s = eval_stmt(r#"id "abc""#, s, &mut e).unwrap();
        let s = eval_stmt("!", s, &mut e).unwrap();
        let s = eval_stmt("id $1", s, &mut e).unwrap();
        assert_eq!(
            s.result_value.downcast_ref::<String>().unwrap().clone(),
            "abc"
        );

        let s = eval_stmt("id x", s, &mut e).unwrap();
        assert_eq!(s.result_value.downcast_ref::<bool>().unwrap().clone(), true);

        let s = eval_stmt("id y", s, &mut e).unwrap();
        assert_eq!(s.result_value.downcast_ref::<i64>().unwrap().clone(), 123);

        let s = eval_stmt("id $1", s, &mut e).unwrap();
        assert_eq!(
            s.result_value.downcast_ref::<String>().unwrap().clone(),
            "abc"
        );

        let s = eval_stmt("(!z id false)", s, &mut e).unwrap();
        let s = eval_stmt("(id z)", s, &mut e).unwrap();
        assert_eq!(
            s.result_value.downcast_ref::<bool>().unwrap().clone(),
            false
        );
        let s = eval_stmt("(id z)", s, &mut e).unwrap();
        let s = eval_stmt("(id _)", s, &mut e).unwrap();
        assert_eq!(
            s.result_value.downcast_ref::<bool>().unwrap().clone(),
            false
        );

        let s = eval_stmt("!-- id (id 555)", s, &mut e).unwrap();
        let s = eval_stmt("id --", s, &mut e).unwrap();
        assert_eq!(s.result_value.downcast_ref::<i64>().unwrap().clone(), 555);

        let s = eval_stmt("!$3 id 3", s, &mut e).unwrap();
        let s = eval_stmt("id $3", s, &mut e).unwrap();
        assert_eq!(s.result_value.downcast_ref::<i64>().unwrap().clone(), 3);

        let s = eval_stmt("! id 2", s, &mut e).unwrap();
        let s = eval_stmt("id $2", s, &mut e).unwrap();
        assert_eq!(s.result_value.downcast_ref::<i64>().unwrap().clone(), 2);

        let s = eval_stmt("! id 4", s, &mut e).unwrap();
        let s = eval_stmt("id $4", s, &mut e).unwrap();
        assert_eq!(s.result_value.downcast_ref::<i64>().unwrap().clone(), 4);
    }
}

// Copyright (c) 2019 Timo Savola. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

use std::any::Any;
use std::collections::HashMap;
use std::num::ParseIntError;
use std::rc::Rc;
use std::result::Result;

use super::parse;
use super::parse::Expr;

static UNDERSCORE: Expr = Expr::Atom("_");

/// Pair may be a node in a singly linked list.
pub struct Pair(pub Rc<dyn Any>, pub Rc<dyn Any>);

/// Ref is a native object stored in an `Rc<dyn Any>`.
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

/// World of primitive values.
pub struct World {
    nil_: Rc<dyn Any>,
    false_: Rc<dyn Any>,
    true_: Rc<dyn Any>,
}

impl World {
    fn new() -> Self {
        World {
            nil_: Rc::new(()),
            false_: Rc::new(false),
            true_: Rc::new(true),
        }
    }

    /// Returns the `()` object.
    pub fn nil(&self) -> Rc<dyn Any> {
        self.nil_.clone()
    }

    /// Returns the `true` object or the `false` object.
    pub fn boolean(&self, value: bool) -> Rc<dyn Any> {
        if value {
            self.true_.clone()
        } else {
            self.false_.clone()
        }
    }
}

struct Form {
    value: Rc<dyn Any>,
    f: fn(&Expr, &mut Frame) -> Result<Rc<dyn Any>, String>,
}

/// Fun is an extension function object.
pub trait Fun {
    fn invoke(&self, w: &World, args: Vec<Rc<dyn Any>>) -> Result<Rc<dyn Any>, String>;
}

/// FunMut is an extension function object with side-effects.
pub trait FunMut {
    fn invoke(&mut self, w: &World, args: Vec<Rc<dyn Any>>) -> Result<Rc<dyn Any>, String>;
}

struct ExtFun<'f> {
    value: Rc<dyn Any>,
    fun: Option<&'f Fun>,
    fun_mut: Option<&'f mut FunMut>,
}

/// Domain of extension functions.
pub struct Domain<'f> {
    world: World,
    forms: HashMap<&'static str, Form>,
    exts: HashMap<&'static str, ExtFun<'f>>,
}

impl<'f> Domain<'f> {
    pub fn new() -> Self {
        let mut domain = Domain {
            world: World::new(),
            forms: HashMap::new(),
            exts: HashMap::new(),
        };

        domain.forms.insert(
            "and",
            Form {
                value: Rc::new(Ref {
                    name: "and",
                    form: true,
                }),
                f: eval_and,
            },
        );

        domain.forms.insert(
            "or",
            Form {
                value: Rc::new(Ref {
                    name: "or",
                    form: true,
                }),
                f: eval_or,
            },
        );

        domain
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
pub struct Binding {
    pub name: String,
    pub value: Rc<dyn Any>,
}

/// Incrementally constructed state.
#[derive(Clone)]
pub struct State {
    inner: Rc<StateLayer>,
    pub result: Binding,
}

impl State {
    pub fn new(domain: &Domain) -> Self {
        State {
            inner: Rc::new(StateLayer {
                parent: None,
                name: "_".to_string(),
                value: domain.world.nil(),
            }),
            result: Binding {
                name: "".to_string(),
                value: domain.world.nil(),
            },
        }
    }
}

struct StateLayer {
    parent: Option<Rc<StateLayer>>,
    name: String,
    value: Rc<dyn Any>,
}

struct Frame<'m, 'f> {
    domain: &'m mut Domain<'f>,
    state: Rc<StateLayer>,
}

/// Parse and evaluate a statement.  A derived state with the result value is
/// returned.
pub fn eval_stmt<'m>(domain: &'m mut Domain, state: State, s: &str) -> Result<State, String> {
    if s.trim().len() == 0 {
        return Ok(State {
            inner: state.inner,
            result: Binding {
                name: "".to_string(),
                value: domain.world.nil(),
            },
        });
    }

    match parse::parse_stmt(s) {
        Ok(ref expr) => {
            let mut frame = Frame {
                domain: domain,
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

                        expr = match p.1 {
                            Expr::Pair(_) => &p.1,
                            Expr::Atom(_) => panic!(),
                            Expr::Nil => &UNDERSCORE,
                        }
                    }
                }
            }

            match eval_stmt_expr(&expr, &mut frame, !s.trim_start().starts_with("(")) {
                Ok(value) => {
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

                    return Ok(State {
                        inner: new,
                        result: Binding {
                            name: name.to_string(),
                            value: value.clone(),
                        },
                    });
                }

                Err(msg) => Err(msg),
            }
        }

        Err(msg) => Err(msg),
    }
}

fn eval_stmt_expr(expr: &Expr, frame: &mut Frame, stmt: bool) -> Result<Rc<dyn Any>, String> {
    match expr {
        Expr::Pair(p) => eval_call(&p, frame, stmt),
        Expr::Atom(s) => eval_atom(s, frame),
        Expr::Nil => Ok(frame.domain.world.nil()),
    }
}

fn eval_expr(expr: &Expr, frame: &mut Frame) -> Result<Rc<dyn Any>, String> {
    eval_stmt_expr(expr, frame, false)
}

fn eval_atom(s: &str, frame: &mut Frame) -> Result<Rc<dyn Any>, String> {
    if s == "false" {
        return Ok(frame.domain.world.boolean(false));
    }
    if s == "true" {
        return Ok(frame.domain.world.boolean(true));
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
        panic!();
    }
}

fn eval_number(s: &str) -> Result<Rc<dyn Any>, String> {
    let r: Result<i64, ParseIntError> = s.parse();
    match r {
        Result::Ok(n) => Ok(Rc::new(n)),
        Err(e) => Err(e.to_string()),
    }
}

fn eval_string(s: &str) -> Result<Rc<dyn Any>, String> {
    if s.len() < 2 {
        panic!();
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

    Ok(Rc::new(buf))
}

fn eval_symbol<'m, 'f>(s: &str, frame: &Frame<'m, 'f>) -> Result<Rc<dyn Any>, String> {
    let mut state = &frame.state;

    loop {
        if state.name == s {
            return Ok(state.value.clone());
        }

        if let Some(ref parent) = state.parent {
            state = parent;
        } else {
            break;
        }
    }

    if let Some(x) = frame.domain.exts.get(s) {
        return Ok(x.value.clone());
    }

    if let Some(x) = frame.domain.forms.get(s) {
        return Ok(x.value.clone());
    }

    Err(s.to_string())
}

fn eval_call(p: &parse::Pair, frame: &mut Frame, stmt: bool) -> Result<Rc<dyn Any>, String> {
    match eval_expr(&p.0, frame) {
        Ok(x) => {
            if let Some(fnref) = x.downcast_ref::<Ref>() {
                if fnref.form {
                    return (frame.domain.forms.get(fnref.name).unwrap().f)(&p.1, frame);
                } else {
                    let mut args = Vec::new();

                    match eval_args(&mut args, &p.1, frame) {
                        None => {
                            if let Some(ext) = frame.domain.exts.get_mut(fnref.name) {
                                if let Some(fun) = ext.fun {
                                    fun.invoke(&frame.domain.world, args)
                                } else if let Some(ref mut fun) = ext.fun_mut {
                                    fun.invoke(&frame.domain.world, args)
                                } else {
                                    panic!();
                                }
                            } else {
                                Err("function implementation is missing".to_string())
                            }
                        }

                        Some(msg) => Err(msg),
                    }
                }
            } else if stmt {
                match p.1 {
                    Expr::Nil => Ok(x),

                    _ => match eval_list(&p.1, frame) {
                        Ok(cdr) => Ok(Rc::new(Pair(x, cdr))),
                        Err(msg) => Err(msg),
                    },
                }
            } else {
                Err("not a function".to_string())
            }
        }

        Err(msg) => Err(msg),
    }
}

fn eval_list(args: &Expr, frame: &mut Frame) -> Result<Rc<dyn Any>, String> {
    match args {
        Expr::Pair(p) => match eval_expr(&p.0, frame) {
            Ok(car) => match eval_list(&p.1, frame) {
                Ok(cdr) => Ok(Rc::new(Pair(car, cdr))),
                Err(msg) => Err(msg),
            },

            Err(msg) => Err(msg),
        },

        Expr::Atom(_) => panic!(),

        Expr::Nil => Ok(frame.domain.world.nil()),
    }
}

fn eval_and(args: &Expr, frame: &mut Frame) -> Result<Rc<dyn Any>, String> {
    match args {
        Expr::Pair(p) => {
            match eval_expr(&p.0, frame) {
                Ok(x) => {
                    if is_truthful(x.clone()) {
                        if let Expr::Nil = p.1 {
                            Ok(x) // Final argument.
                        } else {
                            eval_and(&p.1, frame)
                        }
                    } else {
                        Ok(x)
                    }
                }

                Err(msg) => Err(msg),
            }
        }

        Expr::Atom(_) => panic!(),

        Expr::Nil => Ok(frame.domain.world.boolean(true)),
    }
}

fn eval_or(args: &Expr, frame: &mut Frame) -> Result<Rc<dyn Any>, String> {
    match args {
        Expr::Pair(p) => {
            match eval_expr(&p.0, frame) {
                Ok(x) => {
                    if is_truthful(x.clone()) {
                        Ok(x)
                    } else {
                        if let Expr::Nil = p.1 {
                            Ok(x) // Final argument.
                        } else {
                            eval_or(&p.1, frame)
                        }
                    }
                }

                Err(msg) => Err(msg),
            }
        }

        Expr::Atom(_) => panic!(),

        Expr::Nil => Ok(frame.domain.world.boolean(false)),
    }
}

fn eval_args(dest: &mut Vec<Rc<dyn Any>>, args: &Expr, frame: &mut Frame) -> Option<String> {
    match args {
        Expr::Pair(p) => match eval_expr(&p.0, frame) {
            Ok(x) => {
                dest.push(x);
                eval_args(dest, &p.1, frame)
            }

            Err(msg) => Some(msg),
        },

        Expr::Atom(_) => panic!(),

        Expr::Nil => None,
    }
}

/// Convert an object to a boolean value.  The `()`, `false`, `0` (i64) and
/// `""` (String) values are considered false; all other objects are considered
/// true.
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
        let mut s = String::new();
        s.push('$');
        s.push_str(&i.to_string());
        if let Ok(_) = eval_symbol(&s, frame) {
            continue;
        }
        return s;
    }

    panic!();
}

#[cfg(test)]
mod tests {
    use super::*;

    fn eval<'m>(s: &str, domain: &'m mut Domain) -> Rc<dyn Any> {
        eval_stmt(domain, State::new(&domain), s)
            .unwrap()
            .result
            .value
            .clone()
    }

    struct Id;

    impl Fun for Id {
        fn invoke(&self, _: &World, args: Vec<Rc<dyn Any>>) -> Result<Rc<dyn Any>, String> {
            if args.len() == 1 {
                Ok(args[0].clone())
            } else {
                Err("id: wrong number of arguments".to_string())
            }
        }
    }

    struct Greet {
        greetings: i32,
    }

    impl FunMut for Greet {
        fn invoke(&mut self, w: &World, args: Vec<Rc<dyn Any>>) -> Result<Rc<dyn Any>, String> {
            if let Some(x) = args.first() {
                if let Some(b) = x.downcast_ref::<bool>() {
                    if *b {
                        self.greetings += 1;
                        return Ok(Rc::new("hello, world".to_string()));
                    }
                }
            }

            Ok(w.nil())
        }
    }

    #[test]
    fn test_eval_stmt() {
        let id = Id {};
        let mut greet1 = Greet { greetings: 0 };
        let mut greet2 = Greet { greetings: 0 };
        let mut d = Domain::new();
        d.register("id", &id);
        d.register_mut("greet-1", &mut greet1);
        d.register_mut("greet-2", &mut greet2);

        assert_eq!(*eval("id 123", &mut d).downcast_ref::<i64>().unwrap(), 123);

        assert_eq!(
            *eval("(greet-1 true)", &mut d)
                .downcast_ref::<String>()
                .unwrap(),
            "hello, world"
        );

        assert_eq!(
            *eval("id (id -123)", &mut d).downcast_ref::<i64>().unwrap(),
            -123
        );

        eval("(greet-2 true)", &mut d);
        eval("(greet-2 true)", &mut d);
        eval("(greet-2 false)", &mut d);
        assert_eq!(greet1.greetings, 1);
        assert_eq!(greet2.greetings, 2);
    }

    #[test]
    fn test_eval_string() {
        let id = Id {};
        let mut d = Domain::new();
        d.register("id", &id);

        assert_eq!(
            *eval(r#"id "foo""#, &mut d)
                .downcast_ref::<String>()
                .unwrap(),
            "foo"
        );

        assert_eq!(
            *eval(r#"id "foo\n""#, &mut d)
                .downcast_ref::<String>()
                .unwrap(),
            "foo\n"
        );

        assert_eq!(
            *eval(r#"id "\"foo\"""#, &mut d)
                .downcast_ref::<String>()
                .unwrap(),
            r#""foo""#
        );
    }

    #[test]
    fn test_eval_list() {
        let r = eval("1", &mut Domain::new());
        assert_eq!(*r.downcast_ref::<i64>().unwrap(), 1);

        let r = eval("2 3", &mut Domain::new());
        let head = r.downcast_ref::<Pair>().unwrap();
        assert_eq!(*head.0.downcast_ref::<i64>().unwrap(), 2);
        let tail = head.1.downcast_ref::<Pair>().unwrap();
        assert_eq!(*tail.0.downcast_ref::<i64>().unwrap(), 3);
        tail.1.downcast_ref::<()>().unwrap();

        let r = eval("4 5 6", &mut Domain::new());
        let head = r.downcast_ref::<Pair>().unwrap();
        assert_eq!(*head.0.downcast_ref::<i64>().unwrap(), 4);
        let mid = head.1.downcast_ref::<Pair>().unwrap();
        assert_eq!(*mid.0.downcast_ref::<i64>().unwrap(), 5);
        let tail = mid.1.downcast_ref::<Pair>().unwrap();
        assert_eq!(*tail.0.downcast_ref::<i64>().unwrap(), 6);
        tail.1.downcast_ref::<()>().unwrap();
    }

    #[test]
    fn test_forms() {
        let mut d = Domain::new();

        assert_eq!(*eval("(and)", &mut d).downcast_ref::<bool>().unwrap(), true);
        assert_eq!(
            *eval("(and (and true true) true)", &mut d)
                .downcast_ref::<bool>()
                .unwrap(),
            true
        );
        assert_eq!(
            *eval("(and (and (and (and)) (and)) (and false))", &mut d)
                .downcast_ref::<bool>()
                .unwrap(),
            false
        );

        assert_eq!(*eval("(or)", &mut d).downcast_ref::<bool>().unwrap(), false);
        assert_eq!(
            *eval("(or (or false false) true)", &mut d)
                .downcast_ref::<bool>()
                .unwrap(),
            true
        );
        assert_eq!(
            *eval("(or (or (or (or)) (or)) (or false))", &mut d)
                .downcast_ref::<bool>()
                .unwrap(),
            false
        );
    }

    #[test]
    fn test_state() {
        let id = Id {};
        let mut d = Domain::new();
        d.register("id", &id);

        let s = State::new(&d);

        let s = eval_stmt(&mut d, s, "!x id true").unwrap();
        let s = eval_stmt(&mut d, s, "id x").unwrap();
        assert_eq!(s.result.value.downcast_ref::<bool>().unwrap().clone(), true);
        let s = eval_stmt(&mut d, s, "id _").unwrap();
        assert_eq!(s.result.value.downcast_ref::<bool>().unwrap().clone(), true);

        let s = eval_stmt(&mut d, s, "id 123").unwrap();
        let s = eval_stmt(&mut d, s, "id _").unwrap();
        assert_eq!(s.result.value.downcast_ref::<i64>().unwrap().clone(), 123);
        let s = eval_stmt(&mut d, s, "!y").unwrap();
        let s = eval_stmt(&mut d, s, "id y").unwrap();
        assert_eq!(s.result.value.downcast_ref::<i64>().unwrap().clone(), 123);

        let s = eval_stmt(&mut d, s, r#"id "abc""#).unwrap();
        let s = eval_stmt(&mut d, s, "!").unwrap();
        let s = eval_stmt(&mut d, s, "id $1").unwrap();
        assert_eq!(
            s.result.value.downcast_ref::<String>().unwrap().clone(),
            "abc"
        );

        let s = eval_stmt(&mut d, s, "id x").unwrap();
        assert_eq!(s.result.value.downcast_ref::<bool>().unwrap().clone(), true);

        let s = eval_stmt(&mut d, s, "id y").unwrap();
        assert_eq!(s.result.value.downcast_ref::<i64>().unwrap().clone(), 123);

        let s = eval_stmt(&mut d, s, "id $1").unwrap();
        assert_eq!(
            s.result.value.downcast_ref::<String>().unwrap().clone(),
            "abc"
        );

        let s = eval_stmt(&mut d, s, "(!z id false)").unwrap();
        let s = eval_stmt(&mut d, s, "(id z)").unwrap();
        assert_eq!(
            s.result.value.downcast_ref::<bool>().unwrap().clone(),
            false
        );
        let s = eval_stmt(&mut d, s, "(id z)").unwrap();
        let s = eval_stmt(&mut d, s, "(id _)").unwrap();
        assert_eq!(
            s.result.value.downcast_ref::<bool>().unwrap().clone(),
            false
        );

        let s = eval_stmt(&mut d, s, "!-- id (id 555)").unwrap();
        let s = eval_stmt(&mut d, s, "id --").unwrap();
        assert_eq!(s.result.value.downcast_ref::<i64>().unwrap().clone(), 555);

        let s = eval_stmt(&mut d, s, "!$3 id 3").unwrap();
        let s = eval_stmt(&mut d, s, "id $3").unwrap();
        assert_eq!(s.result.value.downcast_ref::<i64>().unwrap().clone(), 3);

        let s = eval_stmt(&mut d, s, "! id 2").unwrap();
        let s = eval_stmt(&mut d, s, "id $2").unwrap();
        assert_eq!(s.result.value.downcast_ref::<i64>().unwrap().clone(), 2);

        let s = eval_stmt(&mut d, s, "! id 4").unwrap();
        let s = eval_stmt(&mut d, s, "id $4").unwrap();
        assert_eq!(s.result.value.downcast_ref::<i64>().unwrap().clone(), 4);
    }
}

// Copyright (c) 2019 Timo Savola. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

use std::collections::HashMap;
use std::rc::Rc;
use std::result::Result;

use super::obj::{self, Name, Obj, Pair};
use super::parse::parse_stmt;

pub type Res = Result<Obj, String>;

/// Ref is a native object stored in an Obj.
pub struct Ref {
    name: &'static str,
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

/// Fun is an extension function object.
pub trait Fun {
    fn invoke(&self, list: &Obj) -> Res;
}

/// FunMut is an extension function object with side-effects.
pub trait FunMut {
    fn invoke(&mut self, list: &Obj) -> Res;
}

pub(crate) enum FnImpl<'f> {
    Eval(fn(&mut Frame, &Obj) -> Res),
    Fn(fn(&Obj) -> Res),
    Fun(&'f dyn Fun),
    FunMut(&'f mut dyn FunMut),
}

pub(crate) struct FnEntry<'f> {
    pub imp: FnImpl<'f>,
    obj: Obj,
}

/// Domain of extension functions.
pub struct Domain<'f> {
    entries: HashMap<&'static str, FnEntry<'f>>,
}

impl<'f> Domain<'f> {
    pub fn new() -> Self {
        Domain {
            entries: HashMap::new(),
        }
    }

    pub(crate) fn register_eval(&mut self, name: &'static str, f: fn(&mut Frame, &Obj) -> Res) {
        self.entries.insert(
            name,
            FnEntry {
                imp: FnImpl::Eval(f),
                obj: Rc::new(Ref { name: name }),
            },
        );
    }

    pub fn register(&mut self, name: &'static str, f: fn(&Obj) -> Res) {
        self.entries.insert(
            name,
            FnEntry {
                imp: FnImpl::Fn(f),
                obj: Rc::new(Ref { name: name }),
            },
        );
    }

    pub fn register_fun(&mut self, name: &'static str, f: &'f dyn Fun) {
        self.entries.insert(
            name,
            FnEntry {
                imp: FnImpl::Fun(f),
                obj: Rc::new(Ref { name: name }),
            },
        );
    }

    pub fn register_fun_mut(&mut self, name: &'static str, f: &'f mut dyn FunMut) {
        self.entries.insert(
            name,
            FnEntry {
                imp: FnImpl::FunMut(f),
                obj: Rc::new(Ref { name: name }),
            },
        );
    }
}

#[derive(Clone)]
pub struct Binding {
    pub name: String,
    pub value: Obj,
}

/// Incrementally constructed state.
#[derive(Clone)]
pub struct State {
    pub env: Obj,
    pub result: Binding,
}

impl State {
    pub fn new() -> Self {
        let nil = obj::nil();

        State {
            env: obj::pair(
                obj::pair(obj::name("_".to_string()), nil.clone()),
                nil.clone(),
            ),
            result: Binding {
                name: "".to_string(),
                value: nil,
            },
        }
    }

    /// Derive a state with the given result value (bound to `_`).
    pub fn with_result(&self, value: Obj) -> State {
        State {
            env: obj::pair(
                obj::pair(obj::name("_".to_string()), value.clone()),
                cdr(&self.env).clone(), // Skip innermost layer with old _ value.
            ),
            result: Binding {
                name: "_".to_string(),
                value: value,
            },
        }
    }
}

pub(crate) struct Frame<'m, 'f> {
    pub domain: &'m mut Domain<'f>,
    pub env: Obj,
}

impl<'m, 'f> Frame<'m, 'f> {
    pub fn lookup_ref(&mut self, fref: &Ref) -> Option<&mut FnEntry<'f>> {
        self.domain.entries.get_mut(fref.name)
    }
}

/// Parse and evaluate a statement.  A derived state with the result value is
/// returned.
pub fn eval_stmt<'m>(domain: &'m mut Domain, state: State, s: &str) -> Result<State, String> {
    if s.trim_start().len() == 0 {
        return Ok(State {
            env: state.env,
            result: Binding {
                name: "".to_string(),
                value: obj::nil(),
            },
        });
    }

    let (stmt, paren) = parse_stmt(s)?;

    let mut var = "_".to_string();

    let mut frame = Frame {
        domain: domain,
        env: state.env.clone(),
    };

    let value = if paren {
        eval_expr(&mut frame, &stmt)
    } else {
        let head = stmt.downcast_ref::<Pair>().unwrap();

        if let Some(name) = head.0.downcast_ref::<Name>() {
            if name.0.starts_with("!") {
                if name.0.len() == 1 {
                    var = choose_name(&frame);
                } else {
                    var = name.0[1..].to_string();
                }

                if let Some(tail) = head.1.downcast_ref::<Pair>() {
                    // Evaluate "!var (exp)" as "!var exp", but
                    // evaluate "!var (e) x" as it is.
                    if tail.0.is::<Pair>() && tail.1.is::<()>() {
                        eval_expr(&mut frame, &tail.0)
                    } else {
                        eval_toplevel_expr(&mut frame, &head.1)
                    }
                } else {
                    // End of list.
                    eval_name(&mut frame, "_")
                }
            } else {
                eval_toplevel_expr(&mut frame, &stmt)
            }
        } else {
            eval_toplevel_expr(&mut frame, &stmt)
        }
    }?;

    let mut new = obj::pair(
        obj::pair(obj::name(var.to_string()), value.clone()),
        cdr(&state.env).clone(), // Skip innermost layer with old _ value.
    );

    if var != "_" {
        // Bubble old _ value up to innermost new layer.
        new = obj::pair(car(&state.env).clone(), new);
    }

    Ok(State {
        env: new,
        result: Binding {
            name: var.to_string(),
            value: value,
        },
    })
}

fn eval_toplevel_expr(frame: &mut Frame, list_obj: &Obj) -> Res {
    if let Some(result) = eval_call(frame, list_obj.downcast_ref::<Pair>().unwrap()) {
        result
    } else {
        let list_obj = eval_args(frame, list_obj)?;
        let list = list_obj.downcast_ref::<Pair>().unwrap();
        if list.1.is::<()>() {
            Ok(list.0.clone()) // Convert (x) to x.
        } else {
            Ok(list_obj)
        }
    }
}

pub(crate) fn eval_expr(frame: &mut Frame, expr: &Obj) -> Res {
    if let Some(pair) = expr.downcast_ref::<Pair>() {
        match eval_call(frame, pair) {
            Some(result) => result,
            None => expected_function(),
        }
    } else if let Some(name) = expr.downcast_ref::<Name>() {
        eval_name(frame, &name.0)
    } else {
        Ok(expr.clone())
    }
}

fn eval_call(frame: &mut Frame, list: &Pair) -> Option<Res> {
    match eval_expr(frame, &list.0) {
        Ok(x) => {
            let fref = x.downcast_ref::<Ref>()?;
            Some(if let Some(entry) = frame.domain.entries.get(fref.name) {
                if let FnImpl::Eval(f) = entry.imp {
                    f(frame, &list.1)
                } else {
                    match eval_args(frame, &list.1) {
                        Ok(args) => match frame.lookup_ref(fref).unwrap().imp {
                            FnImpl::Fn(f) => f(&args),
                            FnImpl::Fun(ref f) => f.invoke(&args),
                            FnImpl::FunMut(ref mut f) => f.invoke(&args),
                            _ => panic!(),
                        },

                        Err(msg) => Err(msg),
                    }
                }
            } else {
                missing_function()
            })
        }

        Err(msg) => Some(Err(msg)),
    }
}

fn eval_args(frame: &mut Frame, list: &Obj) -> Res {
    Ok(if let Some(pair) = list.downcast_ref::<Pair>() {
        let car = eval_expr(frame, &pair.0)?;
        let cdr = eval_args(frame, &pair.1)?;
        obj::pair(car, cdr)
    } else {
        list.clone() // It must be nil.
    })
}

fn eval_name(frame: &Frame, s: &str) -> Res {
    let mut level = &frame.env.clone();

    loop {
        let binding = car(level).clone();
        if car(&binding).downcast_ref::<Name>().unwrap().0 == s {
            return Ok(cdr(&binding).clone());
        }

        level = cdr(&level);
        if level.is::<()>() {
            break;
        }
    }

    if let Some(x) = frame.domain.entries.get(s) {
        return Ok(x.obj.clone());
    }

    Err(s.to_string())
}

fn choose_name<'m, 'f>(frame: &Frame<'m, 'f>) -> String {
    for i in 1.. {
        let mut s = String::new();
        s.push('$');
        s.push_str(&i.to_string());
        if !eval_name(frame, &s).is_ok() {
            return s;
        }
    }

    panic!();
}

pub(crate) fn expected_function() -> Res {
    Err("not a function".to_string())
}

pub(crate) fn missing_function() -> Res {
    Err("function implementation is missing".to_string())
}

fn car(pair: &Obj) -> &Obj {
    &pair.downcast_ref::<Pair>().unwrap().0
}

fn cdr(pair: &Obj) -> &Obj {
    &pair.downcast_ref::<Pair>().unwrap().1
}

#[cfg(test)]
mod tests {
    use super::*;

    fn eval<'m>(s: &str, d: &'m mut Domain) -> Obj {
        eval_stmt(d, State::new(), s).unwrap().result.value.clone()
    }

    struct Id;

    impl Fun for Id {
        fn invoke(&self, args: &Obj) -> Res {
            if let Some(pair) = args.downcast_ref::<Pair>() {
                if pair.1.is::<()>() {
                    return Ok(pair.0.clone());
                }
            }

            Err("id: wrong number of arguments".to_string())
        }
    }

    struct Greet {
        greetings: i32,
    }

    impl FunMut for Greet {
        fn invoke(&mut self, args: &Obj) -> Res {
            if let Some(pair) = args.downcast_ref::<Pair>() {
                if let Some(b) = pair.0.downcast_ref::<bool>() {
                    if *b {
                        self.greetings += 1;
                        return Ok(obj::string("hello, world".to_string()));
                    }
                }
            }

            Ok(obj::nil())
        }
    }

    #[test]
    fn test_eval_stmt() {
        let id = Id {};
        let mut greet1 = Greet { greetings: 0 };
        let mut greet2 = Greet { greetings: 0 };
        let mut d = Domain::new();
        d.register_fun("id", &id);
        d.register_fun_mut("greet-1", &mut greet1);
        d.register_fun_mut("greet-2", &mut greet2);

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
    fn test_state() {
        let id = Id {};
        let mut d = Domain::new();
        d.register_fun("id", &id);

        let s = State::new();

        let s = eval_stmt(&mut d, s, "!x id true").unwrap();
        let s = eval_stmt(&mut d, s, "id x").unwrap();
        assert_eq!(s.result.value.downcast_ref::<bool>().unwrap().clone(), true);
        let s = eval_stmt(&mut d, s, "x").unwrap();
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

        assert!(eval_stmt(&mut d, s.clone(), "(!z id false)").is_err());

        let s = eval_stmt(&mut d, s, "!z id false").unwrap();
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

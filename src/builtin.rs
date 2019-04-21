// Copyright (c) 2019 Timo Savola. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

use std::any::Any;
use std::rc::Rc;

use super::eval::{is_truthful, Domain, Fun, Pair, World};

fn expected_i64() -> Result<Rc<dyn Any>, String> {
    Err("arithmetic function expects i64".to_string())
}

fn expected_pair() -> Result<Rc<dyn Any>, String> {
    Err("function expects cons pair as argument".to_string())
}

fn wrong_number_of_arguments() -> Result<Rc<dyn Any>, String> {
    Err("wrong number of arguments".to_string())
}

/// Register all optional built-in functions.
pub fn register_all(d: &mut Domain) {
    d.register("+", &ADD);
    d.register("-", &SUB);
    d.register("*", &MUL);
    d.register("/", &DIV);
    d.register("car", &CAR);
    d.register("cdr", &CDR);
    d.register("cons", &CONS);
    d.register("list", &LIST);
    d.register("not", &NOT);
    d.register("identity", &IDENTITY);
}

/// The `+` function.
pub static ADD: Add = Add {};

/// The `-` function.
pub static SUB: Sub = Sub {};

/// The `*` function.
pub static MUL: Mul = Mul {};

/// The `/` function.
pub static DIV: Div = Div {};

/// The `car` function.
pub static CAR: Car = Car {};

/// The `cdr` function.
pub static CDR: Cdr = Cdr {};

/// The `cons` function.
pub static CONS: Cons = Cons {};

/// The `list` function.
pub static LIST: List = List {};

/// The `not` function.
pub static NOT: Not = Not {};

/// The `identity` function.
pub static IDENTITY: Identity = Identity {};

pub struct Add;
pub struct Sub;
pub struct Mul;
pub struct Div;
pub struct Car;
pub struct Cdr;
pub struct Cons;
pub struct List;
pub struct Not;
pub struct Identity;

impl Fun for Add {
    fn invoke(&self, _: &World, args: Vec<Rc<dyn Any>>) -> Result<Rc<dyn Any>, String> {
        let mut res: i64 = 0;

        for x in args {
            if let Some(n) = x.downcast_ref::<i64>() {
                res += n;
            } else {
                return expected_i64();
            }
        }

        Ok(Rc::new(res))
    }
}

impl Fun for Sub {
    fn invoke(&self, _: &World, args: Vec<Rc<dyn Any>>) -> Result<Rc<dyn Any>, String> {
        if args.len() == 0 {
            Ok(Rc::new(0 as i64))
        } else {
            let mut res = if let Some(n) = args[0].downcast_ref::<i64>() {
                *n
            } else {
                return expected_i64();
            };

            if args.len() == 1 {
                res = -res
            } else {
                for x in &args[1..] {
                    if let Some(n) = x.downcast_ref::<i64>() {
                        res -= n;
                    } else {
                        return expected_i64();
                    }
                }
            }

            Ok(Rc::new(res))
        }
    }
}

impl Fun for Mul {
    fn invoke(&self, _: &World, args: Vec<Rc<dyn Any>>) -> Result<Rc<dyn Any>, String> {
        if args.len() == 0 {
            Ok(Rc::new(0 as i64))
        } else {
            let mut res = if let Some(n) = args[0].downcast_ref::<i64>() {
                *n
            } else {
                return expected_i64();
            };

            for x in &args[1..] {
                if let Some(n) = x.downcast_ref::<i64>() {
                    res *= n;
                } else {
                    return expected_i64();
                }
            }

            Ok(Rc::new(res))
        }
    }
}

impl Fun for Div {
    fn invoke(&self, _: &World, args: Vec<Rc<dyn Any>>) -> Result<Rc<dyn Any>, String> {
        if args.len() == 0 {
            Ok(Rc::new(0 as i64))
        } else {
            let mut res = if let Some(n) = args[args.len() - 1].downcast_ref::<i64>() {
                *n
            } else {
                return expected_i64();
            };

            for i in 2..args.len() + 1 {
                if res == 0 {
                    return expected_i64();
                }

                if let Some(n) = args[args.len() - i].downcast_ref::<i64>() {
                    res = *n / res;
                } else {
                    return expected_i64();
                }
            }

            Ok(Rc::new(res))
        }
    }
}

impl Fun for Car {
    fn invoke(&self, _: &World, args: Vec<Rc<dyn Any>>) -> Result<Rc<dyn Any>, String> {
        if args.len() == 1 {
            if let Some(p) = args[0].downcast_ref::<Pair>() {
                Ok(p.0.clone())
            } else {
                expected_pair()
            }
        } else {
            wrong_number_of_arguments()
        }
    }
}

impl Fun for Cdr {
    fn invoke(&self, _: &World, args: Vec<Rc<dyn Any>>) -> Result<Rc<dyn Any>, String> {
        if args.len() == 1 {
            if let Some(p) = args[0].downcast_ref::<Pair>() {
                Ok(p.1.clone())
            } else {
                expected_pair()
            }
        } else {
            wrong_number_of_arguments()
        }
    }
}

impl Fun for Cons {
    fn invoke(&self, _: &World, args: Vec<Rc<dyn Any>>) -> Result<Rc<dyn Any>, String> {
        if args.len() == 2 {
            Ok(Rc::new(Pair(args[0].clone(), args[1].clone())))
        } else {
            wrong_number_of_arguments()
        }
    }
}

impl Fun for List {
    fn invoke(&self, _: &World, args: Vec<Rc<dyn Any>>) -> Result<Rc<dyn Any>, String> {
        let mut tail: Rc<dyn Any> = Rc::new(());
        for i in 0..args.len() {
            tail = Rc::new(Pair(args[args.len() - i - 1].clone(), tail))
        }
        Ok(tail)
    }
}

impl Fun for Not {
    fn invoke(&self, _: &World, args: Vec<Rc<dyn Any>>) -> Result<Rc<dyn Any>, String> {
        if args.len() == 1 {
            Ok(Rc::new(!is_truthful(args[0].clone())))
        } else {
            wrong_number_of_arguments()
        }
    }
}

impl Fun for Identity {
    fn invoke(&self, _: &World, args: Vec<Rc<dyn Any>>) -> Result<Rc<dyn Any>, String> {
        if args.len() == 1 {
            Ok(args[0].clone())
        } else {
            wrong_number_of_arguments()
        }
    }
}

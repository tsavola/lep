// Copyright (c) 2019 Timo Savola. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

use std::any::Any;
use std::rc::Rc;

use super::eval::{is_truthful, Env, Fun};

fn expected_i64() -> Result<Rc<dyn Any>, String> {
    Err("arithmetic function expects i64".to_string())
}

/// Register all optional built-in functions.
pub fn register_all(env: &mut Env) {
    env.register("+", &ADD);
    env.register("-", &SUB);
    env.register("*", &MUL);
    env.register("/", &DIV);
    env.register("identity", &IDENTITY);
    env.register("not", &NOT);
}

pub static ADD: Add = Add {};
pub static SUB: Sub = Sub {};
pub static MUL: Mul = Mul {};
pub static DIV: Div = Div {};
pub static IDENTITY: Identity = Identity {};
pub static NOT: Not = Not {};

pub struct Add;
pub struct Sub;
pub struct Mul;
pub struct Div;
pub struct Identity;
pub struct Not;

impl Fun for Add {
    fn invoke(&self, args: Vec<Rc<dyn Any>>) -> Result<Rc<dyn Any>, String> {
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
    fn invoke(&self, args: Vec<Rc<dyn Any>>) -> Result<Rc<dyn Any>, String> {
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
    fn invoke(&self, args: Vec<Rc<dyn Any>>) -> Result<Rc<dyn Any>, String> {
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
    fn invoke(&self, args: Vec<Rc<dyn Any>>) -> Result<Rc<dyn Any>, String> {
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

impl Fun for Identity {
    fn invoke(&self, args: Vec<Rc<dyn Any>>) -> Result<Rc<dyn Any>, String> {
        if args.len() == 1 {
            Ok(args[0].clone())
        } else {
            return expected_i64();
        }
    }
}

impl Fun for Not {
    fn invoke(&self, args: Vec<Rc<dyn Any>>) -> Result<Rc<dyn Any>, String> {
        if args.len() == 1 {
            Ok(Rc::new(!is_truthful(args[0].clone())))
        } else {
            return expected_i64();
        }
    }
}

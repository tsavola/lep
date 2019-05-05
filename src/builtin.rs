// Copyright (c) 2019 Timo Savola. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

use super::eval::{
    eval_expr, expected_function, missing_function, register_eval, Domain, FnImpl, Frame, Ref,
};
use super::obj;
use super::obj::{Obj, Pair};

/// Convert an object to a boolean value.  The `()`, `false`, `0` (i64) and
/// `""` (String) values are considered false; all other objects are considered
/// true.
pub fn is_truthful(x: &Obj) -> bool {
    if x.is::<()>() {
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

fn sum(value: i64, list: &Obj) -> Option<i64> {
    if let Some(pair) = list.downcast_ref::<Pair>() {
        sum(value + pair.0.downcast_ref::<i64>()?, &pair.1)
    } else {
        Some(value)
    }
}

fn expected_i64() -> Result<Obj, String> {
    Err("arithmetic function expects i64".to_string())
}

fn expected_pair() -> Result<Obj, String> {
    Err("function expects cons pair as argument".to_string())
}

fn wrong_number_of_arguments() -> Result<Obj, String> {
    Err("wrong number of arguments".to_string())
}

/// Register all built-in functions.
pub fn register(d: &mut Domain) {
    register_and(d);
    register_or(d);
    register_add(d);
    register_sub(d);
    register_mul(d);
    register_div(d);
    register_car(d);
    register_cdr(d);
    register_cons(d);
    register_list(d);
    register_not(d);
    register_identity(d);
}

/// Register the special `and` form.
pub fn register_and(d: &mut Domain) {
    register_eval(d, "and", eval_and);
}

fn eval_and(frame: &mut Frame, args: &Obj) -> Result<Obj, String> {
    if let Some(pair) = args.downcast_ref::<Pair>() {
        let x = eval_expr(frame, &pair.0)?;
        if is_truthful(&x) && pair.1.is::<Pair>() {
            eval_and(frame, &pair.1)
        } else {
            Ok(x)
        }
    } else {
        Ok(obj::boolean(true))
    }
}

/// Register the special `or` form.
pub fn register_or(d: &mut Domain) {
    register_eval(d, "or", eval_or);
}

fn eval_or(frame: &mut Frame, args: &Obj) -> Result<Obj, String> {
    if let Some(pair) = args.downcast_ref::<Pair>() {
        let x = eval_expr(frame, &pair.0)?;
        if is_truthful(&x) || pair.1.is::<()>() {
            Ok(x)
        } else {
            eval_or(frame, &pair.1)
        }
    } else {
        Ok(obj::boolean(false))
    }
}

/// Register the `+` function.
pub fn register_add(d: &mut Domain) {
    d.register("+", add);
}

// The `+` function.
pub fn add(args: &Obj) -> Result<Obj, String> {
    match sum(0, args) {
        Some(n) => Ok(obj::int(n)),
        None => expected_i64(),
    }
}

/// Register the `-` function.
pub fn register_sub(d: &mut Domain) {
    d.register("-", sub);
}

// The `-` function.
pub fn sub(args: &Obj) -> Result<Obj, String> {
    if let Some(pair) = args.downcast_ref::<Pair>() {
        if let Some(minuend) = pair.0.downcast_ref::<i64>() {
            if let Some(subtrahend) = sum(0, &pair.1) {
                return Ok(obj::int(minuend - subtrahend));
            }
        }

        expected_i64()
    } else {
        Ok(obj::int(0))
    }
}

/// Register `*` function.
pub fn register_mul(d: &mut Domain) {
    d.register("*", mul);
}

// The `*` function.
pub fn mul(args: &Obj) -> Result<Obj, String> {
    match product(1, args) {
        Some(n) => Ok(obj::int(n)),
        None => expected_i64(),
    }
}

fn product(value: i64, list: &Obj) -> Option<i64> {
    if let Some(pair) = list.downcast_ref::<Pair>() {
        if let Some(n) = pair.0.downcast_ref::<i64>() {
            product(value * n, &pair.1)
        } else {
            None
        }
    } else {
        Some(value)
    }
}

/// Register the `/` function.
pub fn register_div(d: &mut Domain) {
    d.register("/", div);
}

// The `/` function.
pub fn div(args: &Obj) -> Result<Obj, String> {
    if let Some(pair) = args.downcast_ref::<Pair>() {
        if pair.1.is::<Pair>() {
            if let Some(dividend) = pair.0.downcast_ref::<i64>() {
                if let Some(divisor) = product(1, &pair.1) {
                    return Ok(obj::int(dividend / divisor));
                }
            }

            return expected_i64();
        }
    }

    wrong_number_of_arguments()
}

/// Register `car` function.
pub fn register_car(d: &mut Domain) {
    d.register("car", car);
}

// The `car` function.
pub fn car(args: &Obj) -> Result<Obj, String> {
    if let Some(list) = args.downcast_ref::<Pair>() {
        if list.1.is::<()>() {
            return if let Some(arg) = list.0.downcast_ref::<Pair>() {
                Ok(arg.0.clone())
            } else {
                expected_pair()
            };
        }
    }

    wrong_number_of_arguments()
}

/// Register `cdr` function.
pub fn register_cdr(d: &mut Domain) {
    d.register("cdr", cdr);
}

// The `cdr` function.
pub fn cdr(args: &Obj) -> Result<Obj, String> {
    if let Some(list) = args.downcast_ref::<Pair>() {
        if list.1.is::<()>() {
            return if let Some(arg) = list.0.downcast_ref::<Pair>() {
                Ok(arg.0.clone())
            } else {
                expected_pair()
            };
        }
    }

    wrong_number_of_arguments()
}

/// Register `cons` function.
pub fn register_cons(d: &mut Domain) {
    d.register("cons", cons);
}

// The `cons` function.
pub fn cons(args: &Obj) -> Result<Obj, String> {
    if let Some(head) = args.downcast_ref::<Pair>() {
        if let Some(tail) = head.1.downcast_ref::<Pair>() {
            if tail.1.is::<()>() {
                return Ok(obj::pair(head.0.clone(), tail.0.clone()));
            }
        }
    }

    wrong_number_of_arguments()
}

/// Register `list` function.
pub fn register_list(d: &mut Domain) {
    d.register("list", list);
}

// The `list` function.
pub fn list(args: &Obj) -> Result<Obj, String> {
    Ok(args.clone())
}

/// Register `not` function.
pub fn register_not(d: &mut Domain) {
    d.register("not", not);
}

// The `not` function.
pub fn not(args: &Obj) -> Result<Obj, String> {
    if let Some(pair) = args.downcast_ref::<Pair>() {
        if pair.1.is::<()>() {
            return Ok(obj::boolean(!is_truthful(&pair.0)));
        }
    }

    wrong_number_of_arguments()
}

/// Register `identity` function.
pub fn register_identity(d: &mut Domain) {
    d.register("identity", identity);
}

// The `identity` function.
pub fn identity(args: &Obj) -> Result<Obj, String> {
    if let Some(pair) = args.downcast_ref::<Pair>() {
        if pair.1.is::<()>() {
            return Ok(pair.0.clone());
        }
    }

    wrong_number_of_arguments()
}

#[cfg(test)]
mod tests {
    use super::super::eval::{eval_stmt, State};
    use super::*;

    #[test]
    fn test_evaluators() {
        let mut d = Domain::new();
        register_and(&mut d);
        register_or(&mut d);

        let s = State::new();

        let s = eval_stmt(&mut d, s, "(and)").unwrap();
        assert_eq!(*s.result.value.downcast_ref::<bool>().unwrap(), true);

        let s = eval_stmt(&mut d, s, "(and (and true true) true)").unwrap();
        assert_eq!(*s.result.value.downcast_ref::<bool>().unwrap(), true);

        let s = eval_stmt(&mut d, s, "(and (and (and (and)) (and)) (and false))").unwrap();
        assert_eq!(*s.result.value.downcast_ref::<bool>().unwrap(), false);

        let s = eval_stmt(&mut d, s, "(or)").unwrap();
        assert_eq!(*s.result.value.downcast_ref::<bool>().unwrap(), false);

        let s = eval_stmt(&mut d, s, "(or (or false false) true)").unwrap();
        assert_eq!(*s.result.value.downcast_ref::<bool>().unwrap(), true);

        let s = eval_stmt(&mut d, s, "(or (or (or (or)) (or)) (or false))").unwrap();
        assert_eq!(*s.result.value.downcast_ref::<bool>().unwrap(), false);
    }
}

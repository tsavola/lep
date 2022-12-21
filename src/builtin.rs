// Copyright (c) 2019 Timo Savola.
// Use of this source code is governed by the MIT
// license that can be found in the LICENSE file.

use super::eval::{
    eval_expr, expected_function, missing_function, Domain, FnImpl, Frame, Ref, Res,
};
use super::obj::{self, Obj, Pair};

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

fn expected_nonnegative_count() -> Res {
    Err("function expects nonnegative count".to_string())
}

fn expected_i64() -> Res {
    Err("arithmetic function expects i64".to_string())
}

fn expected_pair() -> Res {
    Err("function expects cons pair as argument".to_string())
}

fn wrong_number_of_arguments() -> Res {
    Err("wrong number of arguments".to_string())
}

/// Register all built-in functions.
pub fn register(d: &mut Domain) {
    d.register("*", mul);
    d.register("+", add);
    d.register("-", sub);
    d.register("/", div);
    d.register("car", car);
    d.register("cdr", cdr);
    d.register("cons", cons);
    d.register("drop", drop);
    d.register("list", list);
    d.register("not", not);
    d.register("take", take);
    d.register_eval("and", eval_and);
    d.register_eval("apply", eval_apply);
    d.register_eval("env", env);
    d.register_eval("or", eval_or);
}

fn eval_and(frame: &mut Frame, args: &Obj) -> Res {
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

fn eval_or(frame: &mut Frame, args: &Obj) -> Res {
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

fn eval_apply(frame: &mut Frame, args: &Obj) -> Res {
    if let Some(head) = args.downcast_ref::<Pair>() {
        if let Some(tail) = head.1.downcast_ref::<Pair>() {
            if tail.1.is::<()>() {
                let fexpr = eval_expr(frame, &head.0)?;
                let fargs = eval_expr(frame, &tail.0)?;

                return if let Some(fref) = fexpr.downcast_ref::<Ref>() {
                    if let Some(entry) = frame.lookup_ref(fref) {
                        match entry.imp {
                            FnImpl::Eval(f) => f(frame, &fargs),
                            FnImpl::Fn(f) => f(&fargs),
                            FnImpl::Fun(f) => f.invoke(&fargs),
                            FnImpl::FunMut(ref mut f) => f.invoke(&fargs),
                        }
                    } else {
                        missing_function()
                    }
                } else {
                    expected_function()
                };
            }
        }
    }

    wrong_number_of_arguments()
}

/// The `+` function.
pub fn add(args: &Obj) -> Res {
    match sum(0, args) {
        Some(n) => Ok(obj::int(n)),
        None => expected_i64(),
    }
}

/// The `-` function.
pub fn sub(args: &Obj) -> Res {
    if let Some(pair) = args.downcast_ref::<Pair>() {
        if let Some(first) = pair.0.downcast_ref::<i64>() {
            if pair.1.is::<()>() {
                return Ok(obj::int(-first));
            } else if let Some(subtrahend) = sum(0, &pair.1) {
                return Ok(obj::int(first - subtrahend));
            }
        }

        expected_i64()
    } else {
        Ok(obj::int(0))
    }
}

/// The `*` function.
pub fn mul(args: &Obj) -> Res {
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

/// The `/` function.
pub fn div(args: &Obj) -> Res {
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

/// The `car` function.
pub fn car(args: &Obj) -> Res {
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

/// The `cdr` function.
pub fn cdr(args: &Obj) -> Res {
    if let Some(list) = args.downcast_ref::<Pair>() {
        if list.1.is::<()>() {
            return if let Some(arg) = list.0.downcast_ref::<Pair>() {
                Ok(arg.1.clone())
            } else {
                expected_pair()
            };
        }
    }

    wrong_number_of_arguments()
}

/// The `cons` function.
pub fn cons(args: &Obj) -> Res {
    if let Some(head) = args.downcast_ref::<Pair>() {
        if let Some(tail) = head.1.downcast_ref::<Pair>() {
            if tail.1.is::<()>() {
                return Ok(obj::pair(head.0.clone(), tail.0.clone()));
            }
        }
    }

    wrong_number_of_arguments()
}

/// The `drop` function.
pub fn drop(args: &Obj) -> Res {
    if let Some(pair) = args.downcast_ref::<Pair>() {
        if let Some(count) = pair.0.downcast_ref::<i64>() {
            if *count < 0 {
                return expected_nonnegative_count();
            }

            if let Some(pair) = pair.1.downcast_ref::<Pair>() {
                if pair.1.is::<()>() {
                    let mut res = &pair.0;

                    for _ in 0..*count {
                        if let Some(pair) = res.downcast_ref::<Pair>() {
                            res = &pair.1;
                        } else {
                            return expected_pair();
                        }
                    }

                    return Ok(res.clone());
                }
            }
        } else {
            return expected_i64();
        }
    }

    wrong_number_of_arguments()
}

/// The `take` function.
pub fn take(args: &Obj) -> Res {
    if let Some(pair) = args.downcast_ref::<Pair>() {
        if let Some(count) = pair.0.downcast_ref::<i64>() {
            if *count < 0 {
                return expected_nonnegative_count();
            }

            if let Some(pair) = pair.1.downcast_ref::<Pair>() {
                if pair.1.is::<()>() {
                    return take_n(*count, &pair.0);
                }
            }
        } else {
            return expected_i64();
        }
    }

    wrong_number_of_arguments()
}

fn take_n(count: i64, list: &Obj) -> Res {
    if count == 0 {
        return Ok(obj::nil());
    }

    if let Some(pair) = list.downcast_ref::<Pair>() {
        return Ok(obj::pair(pair.0.clone(), take_n(count-1, &pair.1)?));
    }

    expected_pair()
}

/// The `list` function.
pub fn list(args: &Obj) -> Res {
    Ok(args.clone())
}

/// The `not` function.
pub fn not(args: &Obj) -> Res {
    if let Some(pair) = args.downcast_ref::<Pair>() {
        if pair.1.is::<()>() {
            return Ok(obj::boolean(!is_truthful(&pair.0)));
        }
    }

    wrong_number_of_arguments()
}

fn env(frame: &mut Frame, args: &Obj) -> Res {
    if args.is::<()>() {
        Ok(frame.env.downcast_ref::<Pair>().unwrap().1.clone()) // Skip _.
    } else {
        wrong_number_of_arguments()
    }
}

#[cfg(test)]
mod tests {
    use super::super::eval::{eval_stmt, State};
    use super::*;

    #[test]
    fn test_evaluators() {
        let mut d = Domain::new();
        d.register_eval("and", eval_and);
        d.register_eval("or", eval_or);

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

    #[test]
    fn test_list() {
        let mut d = Domain::new();
        d.register("list", list);

        let s = State::new();

        let s = eval_stmt(&mut d, s, "(list)").unwrap();
        assert!(s.result.value.is::<()>());

        let s = eval_stmt(&mut d, s, "(list 0)").unwrap();
        assert!(s.result.value.is::<Pair>());
    }

    #[test]
    fn test_drop() {
        let mut d = Domain::new();
        d.register("drop", drop);
        d.register("list", list);

        let s = State::new();

        assert!(eval_stmt(&mut d, State::new(), "(drop)").is_err());

        assert!(eval_stmt(&mut d, State::new(), "(drop 0)").is_err());

        assert!(eval_stmt(&mut d, State::new(), "(drop false ())").is_err());

        let s = eval_stmt(&mut d, s, "(drop 0 ())").unwrap();
        assert!(s.result.value.is::<()>());

        assert!(eval_stmt(&mut d, State::new(), "(drop 5 (list 1 2 3 4))").is_err());

        let s = eval_stmt(&mut d, s, "(drop 5 (list 1 2 3 4 5))").unwrap();
        assert!(s.result.value.is::<()>());

        let s = eval_stmt(&mut d, s, "(drop 5 (list 1 2 3 4 5 6))").unwrap();
        assert!(s.result.value.is::<Pair>());
    }

    #[test]
    fn test_take() {
        let mut d = Domain::new();
        d.register("list", list);
        d.register("take", take);

        let s = State::new();

        assert!(eval_stmt(&mut d, State::new(), "(take)").is_err());

        assert!(eval_stmt(&mut d, State::new(), "(take 0)").is_err());

        assert!(eval_stmt(&mut d, State::new(), "(take false ())").is_err());

        let s = eval_stmt(&mut d, s, "(take 0 ())").unwrap();
        assert!(s.result.value.is::<()>());

        let s = eval_stmt(&mut d, s, "(take 0 (list 1 2 3))").unwrap();
        assert!(s.result.value.is::<()>());

        assert!(eval_stmt(&mut d, State::new(), "(take 5 (list 1 2 3 4))").is_err());

        let s = eval_stmt(&mut d, s, "(take 5 (list 1 2 3 4 5))").unwrap();
        assert!(s.result.value.is::<Pair>());

        let s = eval_stmt(&mut d, s, "(take 5 (list 1 2 3 4 5 6))").unwrap();
        assert!(s.result.value.is::<Pair>());
    }
}

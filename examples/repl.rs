// Copyright (c) 2019 Timo Savola. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

use std::any::Any;
use std::rc::Rc;
use std::time::{SystemTime, UNIX_EPOCH};

use rustyline::error::ReadlineError;
use rustyline::Editor;

use lep::{builtin, eval_stmt, stringify, Env, Fun, FunMut, State};

struct Sequence {
    n: i64,
}

impl FunMut for Sequence {
    fn invoke(&mut self, args: Vec<Rc<dyn Any>>) -> Option<Rc<dyn Any>> {
        if args.len() == 0 {
            self.n += 1;
            Some(Rc::new(self.n))
        } else {
            None
        }
    }
}

struct Time;

impl Fun for Time {
    fn invoke(&self, args: Vec<Rc<dyn Any>>) -> Option<Rc<dyn Any>> {
        if args.is_empty() {
            if let Ok(n) = SystemTime::now().duration_since(UNIX_EPOCH) {
                return Some(Rc::new(n.as_secs() as i64));
            }
        }

        None
    }
}

fn main() {
    let mut sequence = Sequence { n: -1 };
    let time = Time {};

    let mut env = Env::new();
    builtin::register_all(&mut env);
    env.register_mut("sequence", &mut sequence);
    env.register("time", &time);

    let mut state = State::new();

    let mut rl = Editor::<()>::new();
    let mut prefix = "".to_string();

    loop {
        match rl.readline(&format!("{}>> ", prefix)) {
            Ok(line) => {
                rl.add_history_entry(line.as_ref());

                if let Some(res) = eval_stmt(&line, state.clone(), &mut env) {
                    if let Some(repr) = stringify(res.result_value.clone()) {
                        if repr.is_empty() {
                            if res.result_name == "_" {
                                prefix = "".to_string();
                            } else if !res.result_name.is_empty() {
                                println!("{} = ()", res.result_name);
                            }
                        } else {
                            if res.result_name == "_" {
                                prefix = repr + " ";
                            } else if !res.result_name.is_empty() {
                                println!("{} = {}", res.result_name, repr);
                            }
                        }
                    } else {
                        if res.result_name == "_" {
                            prefix = "? ".to_string();
                        } else if !res.result_name.is_empty() {
                            println!("{} = ?", res.result_name);
                        }
                    }

                    state = res;
                } else {
                    println!("evaluation error");
                }
            }
            Err(ReadlineError::Eof) => {
                break;
            }
            Err(x) => {
                println!("read error: {}", x);
            }
        }
    }
}

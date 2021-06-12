// Copyright (c) 2019 Timo Savola.
// Use of this source code is governed by the MIT
// license that can be found in the LICENSE file.

use std::process::exit;
use std::time::{SystemTime, UNIX_EPOCH};

use rustyline::error::ReadlineError;
use rustyline::Editor;

use lep::{builtin, eval_stmt, obj, stringify, Domain, Fun, FunMut, Obj, Res, State};

struct Sequence {
    n: i64,
}

impl FunMut for Sequence {
    fn invoke(&mut self, args: &Obj) -> Res {
        if args.is::<()>() {
            self.n += 1;
            Ok(obj::int(self.n))
        } else {
            Err("sequence: too many arguments".to_string())
        }
    }
}

struct Time;

impl Fun for Time {
    fn invoke(&self, args: &Obj) -> Res {
        if args.is::<()>() {
            match SystemTime::now().duration_since(UNIX_EPOCH) {
                Ok(n) => Ok(obj::int(n.as_secs() as i64)),
                Err(e) => Err(format!("time: {}", e)),
            }
        } else {
            Err("time: too many arguments".to_string())
        }
    }
}

fn main() {
    let mut sequence = Sequence { n: -1 };
    let time = Time {};

    let mut domain = Domain::new();
    builtin::register(&mut domain);
    domain.register_fun_mut("sequence", &mut sequence);
    domain.register_fun("time", &time);

    let mut state = State::new();

    let mut rl = Editor::<()>::new();
    let mut prefix = "".to_string();

    loop {
        match rl.readline(&format!("{}>> ", prefix)) {
            Ok(line) => {
                rl.add_history_entry(&line);

                match eval_stmt(&mut domain, state.clone(), &line) {
                    Ok(res) => {
                        if res.result.value.is::<()>() {
                            if res.result.name == "_" {
                                prefix = "".to_string();
                            } else if !res.result.name.is_empty() {
                                println!("{} = ()", res.result.name);
                            }
                        } else {
                            let repr = stringify(&res.result.value).unwrap_or("?".to_string());
                            if res.result.name == "_" {
                                prefix = repr + " ";
                            } else if !res.result.name.is_empty() {
                                println!("{} = {}", res.result.name, repr);
                            }
                        }

                        state = res;
                    }

                    Err(msg) => {
                        println!("error: {}", msg);
                    }
                }
            }

            Err(ReadlineError::Eof) => {
                break;
            }

            Err(x) => {
                println!("read error: {}", x);
                exit(1);
            }
        }
    }
}

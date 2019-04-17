// Copyright (c) 2019 Timo Savola. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

pub enum Expr<'a> {
    Pair(Box<Pair<'a>>),
    Atom(&'a str),
    Nil,
}

pub struct Pair<'a>(pub Expr<'a>, pub Expr<'a>);

pub fn parse_stmt(s: &str) -> Option<Expr> {
    let s = s.trim_start();
    if s.starts_with("(") {
        parse(s)
    } else {
        let (x, n) = parse_tail(s, false);
        if s[s.len() - n..].trim().len() == 0 {
            x
        } else {
            None
        }
    }
}

fn parse(s: &str) -> Option<Expr> {
    let (x, n) = parse_expr(s);
    if s[s.len() - n..].trim().len() == 0 {
        x
    } else {
        None
    }
}

fn parse_expr(s: &str) -> (Option<Expr>, usize) {
    let s = s.trim_start();
    match s.chars().nth(0) {
        Some('(') => parse_tail(&s[1..], true),
        Some(_) => parse_atom(s),
        None => (None, s.len()),
    }
}

fn parse_atom(s: &str) -> (Option<Expr>, usize) {
    if s.chars().nth(0).unwrap() == '"' {
        return parse_string(s);
    }

    let mut offset = 0;

    for c in s.chars() {
        if c == ')' || c.is_whitespace() {
            return (Some(Expr::Atom(&s[..offset])), s.len() - offset);
        }

        if c == '(' {
            return (None, s.len());
        }

        offset += c.len_utf8();
    }

    (Some(Expr::Atom(s)), 0)
}

fn parse_string(s: &str) -> (Option<Expr>, usize) {
    let mut it = s.chars().enumerate();
    it.next(); // Skip first quote.

    let mut offset = 1;
    let mut skip = false;

    for (i, c) in it {
        offset += c.len_utf8();

        if skip {
            skip = false;
            continue;
        }

        match c {
            '\\' => {
                skip = true;
            }

            '"' => {
                let i = i + 1; // Skip last quote.

                if let Some(c) = s.chars().nth(i) {
                    if !(c == ')' || c.is_whitespace()) {
                        return (None, s.len());
                    }
                }

                return (Some(Expr::Atom(&s[..offset])), s.len() - offset);
            }

            _ => {}
        }
    }

    dbg!(s);
    (None, s.len())
}

fn parse_tail(s: &str, paren: bool) -> (Option<Expr>, usize) {
    let s = s.trim_start();
    if let Some(c) = s.chars().nth(0) {
        match c {
            ')' => (Some(Expr::Nil), s.len() - 1),
            _ => {
                let (car, n) = parse_expr(s);
                match car {
                    Some(x) => {
                        let (cdr, n) = parse_tail(&s[s.len() - n..], paren);
                        if let Some(y) = cdr {
                            (Some(Expr::Pair(Box::new(Pair(x, y)))), n)
                        } else {
                            (None, n)
                        }
                    }
                    None => (None, n),
                }
            }
        }
    } else if paren {
        (None, s.len())
    } else {
        (Some(Expr::Nil), 0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_atom() {
        match parse("foo").unwrap() {
            Expr::Atom(s) => assert_eq!(s, "foo"),
            _ => assert!(false),
        }

        assert!(parse("foo bar").is_none());
        assert!(parse("foo)").is_none());
        assert!(parse("foo(").is_none());
        assert!(parse("foo ()").is_none());
    }

    #[test]
    fn test_parse_string() {
        match parse(r#""foo""#).unwrap() {
            Expr::Atom(s) => assert_eq!(s, r#""foo""#),
            _ => assert!(false),
        }

        match parse(r#""foo bar""#).unwrap() {
            Expr::Atom(s) => assert_eq!(s, r#""foo bar""#),
            _ => assert!(false),
        }

        assert!(parse(r#""foo" bar"#).is_none());
        assert!(parse(r#""foo"bar"#).is_none());
        assert!(parse(r#""foo""bar""#).is_none());
        assert!(parse(r#""foo")"#).is_none());
        assert!(parse(r#""foo" ()"#).is_none());

        match parse(r#""foo\n""#).unwrap() {
            Expr::Atom(s) => assert_eq!(s, r#""foo\n""#),
            _ => assert!(false),
        }

        match parse(r#""\"foo\"""#).unwrap() {
            Expr::Atom(s) => assert_eq!(s, r#""\"foo\"""#),
            _ => assert!(false),
        }
    }

    #[test]
    fn test_parse_stmt() {
        match parse_stmt("(foo)").unwrap() {
            Expr::Pair(p) => {
                match p.0 {
                    Expr::Atom(s) => assert_eq!(s, "foo"),
                    _ => assert!(false),
                }
                match p.1 {
                    Expr::Nil => {}
                    _ => assert!(false),
                }
            }
            _ => assert!(false),
        }

        match parse_stmt(" ( foo ) ").unwrap() {
            Expr::Pair(p) => {
                match p.0 {
                    Expr::Atom(s) => assert_eq!(s, "foo"),
                    _ => assert!(false),
                }
                match p.1 {
                    Expr::Nil => {}
                    _ => assert!(false),
                }
            }
            _ => assert!(false),
        }

        match parse_stmt(r#"("foo")"#).unwrap() {
            Expr::Pair(p) => {
                match p.0 {
                    Expr::Atom(s) => assert_eq!(s, r#""foo""#),
                    _ => assert!(false),
                }
                match p.1 {
                    Expr::Nil => {}
                    _ => assert!(false),
                }
            }
            _ => assert!(false),
        }

        match parse_stmt("(foo 123)").unwrap() {
            Expr::Pair(p) => {
                match p.0 {
                    Expr::Atom(s) => assert_eq!(s, "foo"),
                    _ => assert!(false),
                }
                match p.1 {
                    Expr::Pair(p) => {
                        match p.0 {
                            Expr::Atom(s) => assert_eq!(s, "123"),
                            _ => assert!(false),
                        }
                        match p.1 {
                            Expr::Nil => {}
                            _ => assert!(false),
                        }
                    }
                    _ => assert!(false),
                }
            }
            _ => assert!(false),
        }

        match parse_stmt(r#"(foo "bar")"#).unwrap() {
            Expr::Pair(p) => {
                match p.0 {
                    Expr::Atom(s) => assert_eq!(s, "foo"),
                    _ => assert!(false),
                }
                match p.1 {
                    Expr::Pair(p) => {
                        match p.0 {
                            Expr::Atom(s) => assert_eq!(s, r#""bar""#),
                            _ => assert!(false),
                        }
                        match p.1 {
                            Expr::Nil => {}
                            _ => assert!(false),
                        }
                    }
                    _ => assert!(false),
                }
            }
            _ => assert!(false),
        }
    }
}

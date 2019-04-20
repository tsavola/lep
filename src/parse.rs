// Copyright (c) 2019 Timo Savola. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

pub enum Expr<'a> {
    Pair(Box<Pair<'a>>),
    Atom(&'a str),
    Nil,
}

pub struct Pair<'a>(pub Expr<'a>, pub Expr<'a>);

pub fn parse_stmt(s: &str) -> Result<Expr, String> {
    let s = s.trim_start();

    if s.starts_with("(") {
        parse(s)
    } else {
        match parse_tail(s, false) {
            Ok((expr, n)) => {
                if s[s.len() - n..].trim().len() == 0 {
                    Ok(expr)
                } else {
                    Err("statement parse error".to_string())
                }
            }

            Err(msg) => Err(msg),
        }
    }
}

fn parse(s: &str) -> Result<Expr, String> {
    match parse_expr(s) {
        Ok((expr, n)) => {
            if s[s.len() - n..].trim().len() == 0 {
                Ok(expr)
            } else {
                Err("expression parse error".to_string())
            }
        }

        Err(msg) => Err(msg),
    }
}

fn parse_expr(s: &str) -> Result<(Expr, usize), String> {
    let s = s.trim_start();

    match s.chars().nth(0).unwrap() {
        '(' => parse_tail(&s[1..], true),
        _ => parse_atom(s),
    }
}

fn parse_atom(s: &str) -> Result<(Expr, usize), String> {
    if s.chars().nth(0).unwrap() == '"' {
        return parse_string(s);
    }

    let mut offset = 0;

    for c in s.chars() {
        if c == ')' || c.is_whitespace() {
            return Ok((Expr::Atom(&s[..offset]), s.len() - offset));
        }

        if c == '(' {
            return Err("opening paren inside atom".to_string());
        }

        offset += c.len_utf8();
    }

    Ok((Expr::Atom(s), 0))
}

fn parse_string(s: &str) -> Result<(Expr, usize), String> {
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
                        return Err("garbage after string literal".to_string());
                    }
                }

                return Ok((Expr::Atom(&s[..offset]), s.len() - offset));
            }

            _ => {}
        }
    }

    Err("string literal has no closing quote".to_string())
}

fn parse_tail(s: &str, paren: bool) -> Result<(Expr, usize), String> {
    let s = s.trim_start();

    if let Some(c) = s.chars().nth(0) {
        if c == ')' {
            if let Some(c) = s.chars().nth(1) {
                if !(c == ')' || c.is_whitespace()) {
                    return Err("garbage after closing paren".to_string());
                }
            }

            return Ok((Expr::Nil, s.len() - 1));
        }

        match parse_expr(s) {
            Ok((car, n)) => match parse_tail(&s[s.len() - n..], paren) {
                Ok((cdr, n)) => Ok((Expr::Pair(Box::new(Pair(car, cdr))), n)),
                Err(msg) => Err(msg),
            },

            Err(msg) => Err(msg),
        }
    } else if paren {
        Err("expression has no closing paren".to_string())
    } else {
        Ok((Expr::Nil, 0))
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

        assert!(parse("foo bar").is_err());
        assert!(parse("foo)").is_err());
        assert!(parse("foo(").is_err());
        assert!(parse("foo ()").is_err());
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

        assert!(parse(r#""foo" bar"#).is_err());
        assert!(parse(r#""foo"bar"#).is_err());
        assert!(parse(r#""foo""bar""#).is_err());
        assert!(parse(r#""foo")"#).is_err());
        assert!(parse(r#""foo" ()"#).is_err());

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

        parse_stmt(r#"foo()"#).is_err();
        parse_stmt(r#"(foo)()"#).is_err();
        parse_stmt(r#"(foo)bar"#).is_err();
    }
}

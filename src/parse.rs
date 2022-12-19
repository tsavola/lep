// Copyright (c) 2019 Timo Savola.
// Use of this source code is governed by the MIT
// license that can be found in the LICENSE file.

use super::obj::{self, Obj};

pub(crate) fn parse_stmt(s: &str) -> Result<(Obj, bool), String> {
    let mut s = s.trim_start();
    let mut paren = false;

    if s.starts_with('(') {
        s = &s[1..];
        paren = true;
    }

    let (car, n) = parse_tail(s, paren)?;
    let t = s[s.len() - n..].trim_start();
    if t.is_empty() {
        Ok((car, paren))
    } else {
        // Trailing terms after parenthesized first term; add top-level pair.
        let (cdr, _) = parse_tail(t, false)?;
        Ok((obj::pair(car, cdr), false))
    }
}

pub(crate) fn parse_expr(s: &str) -> Result<(Obj, usize), String> {
    let s = s.trim_start();

    match s.chars().next().unwrap() {
        '(' => parse_tail(&s[1..], true),
        _ => parse_atom(s),
    }
}

fn parse_atom(s: &str) -> Result<(Obj, usize), String> {
    if s.starts_with('"') {
        parse_string(s)
    } else {
        parse_nonstring(s)
    }
}

fn parse_string(s: &str) -> Result<(Obj, usize), String> {
    let mut it = s.chars().enumerate();
    it.next(); // Skip first quote.

    let mut offset = 1;
    let mut buf = String::new();
    let mut escape = false;

    for (i, c) in it {
        offset += c.len_utf8();

        if escape {
            match c {
                't' => buf.push('\t'),
                'n' => buf.push('\n'),
                'r' => buf.push('\r'),
                _ => buf.push(c),
            }

            escape = false;
        } else {
            match c {
                '\\' => {
                    escape = true;
                }

                '"' => {
                    let i = i + 1; // Skip last quote.

                    if let Some(c) = s.chars().nth(i) {
                        if !(c == ')' || c.is_whitespace()) {
                            return Err("garbage after string literal".to_string());
                        }
                    }

                    return Ok((obj::string(buf), s.len() - offset));
                }

                _ => buf.push(c),
            }
        }
    }

    Err("string literal has no closing quote".to_string())
}

fn parse_nonstring(s: &str) -> Result<(Obj, usize), String> {
    let mut offset = 0;

    for c in s.chars() {
        if c == ')' || c.is_whitespace() {
            return match atom_object(&s[..offset]) {
                Ok(x) => Ok((x, s.len() - offset)),
                Err(msg) => Err(msg),
            };
        }

        if c == '(' {
            return Err("opening paren inside atom".to_string());
        }

        offset += c.len_utf8();
    }

    match atom_object(s) {
        Ok(x) => Ok((x, 0)),
        Err(msg) => Err(msg),
    }
}

fn atom_object(s: &str) -> Result<Obj, String> {
    match s {
        "false" => Ok(obj::boolean(false)),
        "true" => Ok(obj::boolean(true)),

        _ => {
            let c = s.chars().next().unwrap();
            if c == '-' {
                if let Some(c) = s.chars().nth(1) {
                    if ('0'..='9').contains(&c) {
                        return atom_int(s);
                    }
                }
            } else if ('0'..='9').contains(&c) {
                return atom_int(s);
            }

            Ok(obj::name(s.to_string()))
        }
    }
}

fn atom_int(s: &str) -> Result<Obj, String> {
    match s.parse() {
        Ok(n) => Ok(obj::int(n)),
        Err(e) => Err(e.to_string()),
    }
}

fn parse_tail(s: &str, paren: bool) -> Result<(Obj, usize), String> {
    let s = s.trim_start();

    if let Some(c) = s.chars().next() {
        if c == ')' {
            if let Some(c) = s.chars().nth(1) {
                if !(c == ')' || c.is_whitespace()) {
                    return Err("garbage after closing paren".to_string());
                }
            }

            return Ok((obj::nil(), s.len() - 1));
        }

        let (car, n) = parse_expr(s)?;
        let (cdr, n) = parse_tail(&s[s.len() - n..], paren)?;
        Ok((obj::pair(car, cdr), n))
    } else if paren {
        Err("expression has no closing paren".to_string())
    } else {
        Ok((obj::nil(), 0))
    }
}

#[cfg(test)]
mod tests {
    use super::obj::{Name, Obj, Pair};
    use super::*;

    fn parse(s: &str) -> Result<Obj, String> {
        match parse_expr(s) {
            Ok((obj, n)) => {
                if s[s.len() - n..].trim().len() == 0 {
                    Ok(obj)
                } else {
                    Err("expression parse error".to_string())
                }
            }

            Err(msg) => Err(msg),
        }
    }

    #[test]
    fn test_parse_atom() {
        assert_eq!(
            parse("foo").unwrap().downcast_ref::<Name>().unwrap().0,
            "foo"
        );

        assert!(parse("foo bar").is_err());
        assert!(parse("foo)").is_err());
        assert!(parse("foo(").is_err());
        assert!(parse("foo ()").is_err());
    }

    #[test]
    fn test_parse_string() {
        assert_eq!(
            *parse(r#""foo""#).unwrap().downcast_ref::<String>().unwrap(),
            "foo"
        );

        assert_eq!(
            *parse(r#""foo bar""#)
                .unwrap()
                .downcast_ref::<String>()
                .unwrap(),
            "foo bar"
        );

        assert!(parse(r#""foo" bar"#).is_err());
        assert!(parse(r#""foo"bar"#).is_err());
        assert!(parse(r#""foo""bar""#).is_err());
        assert!(parse(r#""foo")"#).is_err());
        assert!(parse(r#""foo" ()"#).is_err());

        assert_eq!(
            *parse(r#""foo\n""#)
                .unwrap()
                .downcast_ref::<String>()
                .unwrap(),
            "foo\n"
        );

        assert_eq!(
            *parse(r#""\"foo\"""#)
                .unwrap()
                .downcast_ref::<String>()
                .unwrap(),
            r#""foo""#
        );
    }

    #[test]
    fn test_parse_stmt() {
        let r = parse_stmt("(foo)").unwrap();
        let p = r.0.downcast_ref::<Pair>().unwrap();
        assert_eq!(p.0.downcast_ref::<Name>().unwrap().0, "foo");
        p.1.downcast_ref::<()>().unwrap();

        let r = parse_stmt(" ( foo ) ").unwrap();
        let p = r.0.downcast_ref::<Pair>().unwrap();
        assert_eq!(p.0.downcast_ref::<Name>().unwrap().0, "foo");
        p.1.downcast_ref::<()>().unwrap();

        let r = parse_stmt(r#"("foo")"#).unwrap();
        let p = r.0.downcast_ref::<Pair>().unwrap();
        assert_eq!(*p.0.downcast_ref::<String>().unwrap(), "foo");
        p.1.downcast_ref::<()>().unwrap();

        let r = parse_stmt("(foo 123)").unwrap();
        let head = r.0.downcast_ref::<Pair>().unwrap();
        assert_eq!(head.0.downcast_ref::<Name>().unwrap().0, "foo");
        let tail = head.1.downcast_ref::<Pair>().unwrap();
        assert_eq!(*tail.0.downcast_ref::<i64>().unwrap(), 123);
        tail.1.downcast_ref::<()>().unwrap();

        let r = parse_stmt(r#"(foo "bar")"#).unwrap();
        let head = r.0.downcast_ref::<Pair>().unwrap();
        assert_eq!(head.0.downcast_ref::<Name>().unwrap().0, "foo");
        let tail = head.1.downcast_ref::<Pair>().unwrap();
        assert_eq!(*tail.0.downcast_ref::<String>().unwrap(), "bar");
        tail.1.downcast_ref::<()>().unwrap();

        let r = parse_stmt("(foo) bar").unwrap();
        let head = r.0.downcast_ref::<Pair>().unwrap();
        head.0.downcast_ref::<Pair>().unwrap();
        let tail = head.1.downcast_ref::<Pair>().unwrap();
        assert_eq!(tail.0.downcast_ref::<Name>().unwrap().0, "bar");
        tail.1.downcast_ref::<()>().unwrap();

        parse_stmt(r#"foo()"#).unwrap_err();
        parse_stmt(r#"(foo)()"#).unwrap_err();
        parse_stmt(r#"(foo)bar"#).unwrap_err();
    }
}

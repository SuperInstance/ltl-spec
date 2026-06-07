//! Recursive-descent parser for LTL formulas.
//!
//! Supports the following concrete syntax:
//!
//! | Token | Meaning |
//! |-------|---------|
//! | `G` | Globally (always) |
//! | `F` | Finally (eventually) |
//! | `X` | Next |
//! | `U` | Until |
//! | `R` | Release |
//! | `!` | Negation |
//! | `&` | Conjunction |
//! | `\|` | Disjunction |
//! | `->` | Implication |
//! | `globally` / `always` | Globally (alias) |
//! | `eventually` | Finally (alias) |
//! | `next` | Next (alias) |
//! | `until` | Until (alias) |
//! | `release` | Release (alias) |
//!
//! Precedence (lowest to highest):
//! implication → until/release → or → and → not/unary temporal → atomic

use crate::formula::LtlFormula;

/// Parse an LTL formula string into an [`LtlFormula`].
///
/// # Errors
///
/// Returns a string describing the parse error.
///
/// # Examples
///
/// ```
/// use ltl_spec::parse;
/// let f = parse("G(p -> F(q))").unwrap();
/// assert_eq!(f.to_string(), "G((p -> F(q)))");
/// ```
pub fn parse(input: &str) -> Result<LtlFormula, String> {
    let tokens = tokenize(input)?;
    let mut pos = 0;
    let result = parse_implies(&tokens, &mut pos)?;
    if pos < tokens.len() {
        Err(format!(
            "Unexpected token '{}' at position {}",
            tokens[pos], pos
        ))
    } else {
        Ok(result)
    }
}

/// Token representation.
#[derive(Debug, Clone, PartialEq)]
enum Token {
    Atom(String),
    Not,
    And,
    Or,
    Implies,
    LParen,
    RParen,
    Globally,
    Finally,
    Next,
    Until,
    Release,
}

impl std::fmt::Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Token::Atom(s) => write!(f, "{s}"),
            Token::Not => write!(f, "!"),
            Token::And => write!(f, "&"),
            Token::Or => write!(f, "|"),
            Token::Implies => write!(f, "->"),
            Token::LParen => write!(f, "("),
            Token::RParen => write!(f, ")"),
            Token::Globally => write!(f, "G"),
            Token::Finally => write!(f, "F"),
            Token::Next => write!(f, "X"),
            Token::Until => write!(f, "U"),
            Token::Release => write!(f, "R"),
        }
    }
}

fn tokenize(input: &str) -> Result<Vec<Token>, String> {
    let chars: Vec<char> = input.chars().collect();
    let mut tokens = Vec::new();
    let mut i = 0;

    while i < chars.len() {
        match chars[i] {
            ' ' | '\t' | '\n' | '\r' => {
                i += 1;
            }
            '(' => {
                tokens.push(Token::LParen);
                i += 1;
            }
            ')' => {
                tokens.push(Token::RParen);
                i += 1;
            }
            '!' => {
                tokens.push(Token::Not);
                i += 1;
            }
            '&' => {
                tokens.push(Token::And);
                i += 1;
            }
            '|' => {
                tokens.push(Token::Or);
                i += 1;
            }
            '-' if i + 1 < chars.len() && chars[i + 1] == '>' => {
                tokens.push(Token::Implies);
                i += 2;
            }
            '-' => return Err(format!("Unexpected '-' at index {i}")),
            _ => {
                // Read a word (identifier or keyword)
                let start = i;
                while i < chars.len()
                    && !matches!(
                        chars[i],
                        ' ' | '\t' | '\n' | '\r' | '(' | ')' | '!' | '&' | '|' | '-'
                    )
                {
                    i += 1;
                }
                let word: String = chars[start..i].iter().collect();
                let tok = match word.as_str() {
                    "G" | "globally" | "always" => Token::Globally,
                    "F" | "eventually" | "eventally" => Token::Finally,
                    "X" | "next" => Token::Next,
                    "U" | "until" => Token::Until,
                    "R" | "release" => Token::Release,
                    w => {
                        if w.is_empty() {
                            return Err(format!("Empty token at index {start}"));
                        }
                        // Validate: must be alphanumeric/underscore
                        if w.chars().all(|c| c.is_alphanumeric() || c == '_') {
                            Token::Atom(w.to_string())
                        } else {
                            return Err(format!("Invalid atom '{w}' at index {start}"));
                        }
                    }
                };
                tokens.push(tok);
            }
        }
    }

    Ok(tokens)
}

/// implication → until_expr (-> implication)?
fn parse_implies(tokens: &[Token], pos: &mut usize) -> Result<LtlFormula, String> {
    let left = parse_until_release(tokens, pos)?;
    if *pos < tokens.len() && tokens[*pos] == Token::Implies {
        *pos += 1;
        let right = parse_implies(tokens, pos)?;
        Ok(LtlFormula::Implies(Box::new(left), Box::new(right)))
    } else {
        Ok(left)
    }
}

/// until_release → or_expr ((U | R) until_release)?
fn parse_until_release(tokens: &[Token], pos: &mut usize) -> Result<LtlFormula, String> {
    let left = parse_or(tokens, pos)?;
    if *pos < tokens.len() {
        match &tokens[*pos] {
            Token::Until => {
                *pos += 1;
                let right = parse_until_release(tokens, pos)?;
                Ok(LtlFormula::Until(Box::new(left), Box::new(right)))
            }
            Token::Release => {
                *pos += 1;
                let right = parse_until_release(tokens, pos)?;
                Ok(LtlFormula::Release(Box::new(left), Box::new(right)))
            }
            _ => Ok(left),
        }
    } else {
        Ok(left)
    }
}

/// or → and_expr (| or_expr)?
fn parse_or(tokens: &[Token], pos: &mut usize) -> Result<LtlFormula, String> {
    let left = parse_and(tokens, pos)?;
    if *pos < tokens.len() && tokens[*pos] == Token::Or {
        *pos += 1;
        let right = parse_or(tokens, pos)?;
        Ok(LtlFormula::Or(Box::new(left), Box::new(right)))
    } else {
        Ok(left)
    }
}

/// and → unary_expr (& and_expr)?
fn parse_and(tokens: &[Token], pos: &mut usize) -> Result<LtlFormula, String> {
    let left = parse_unary(tokens, pos)?;
    if *pos < tokens.len() && tokens[*pos] == Token::And {
        *pos += 1;
        let right = parse_and(tokens, pos)?;
        Ok(LtlFormula::And(Box::new(left), Box::new(right)))
    } else {
        Ok(left)
    }
}

/// unary → ! unary | G unary | F unary | X unary | primary
fn parse_unary(tokens: &[Token], pos: &mut usize) -> Result<LtlFormula, String> {
    if *pos >= tokens.len() {
        return Err("Unexpected end of input".to_string());
    }
    match &tokens[*pos] {
        Token::Not => {
            *pos += 1;
            let inner = parse_unary(tokens, pos)?;
            Ok(LtlFormula::Not(Box::new(inner)))
        }
        Token::Globally => {
            *pos += 1;
            let inner = parse_unary(tokens, pos)?;
            Ok(LtlFormula::Globally(Box::new(inner)))
        }
        Token::Finally => {
            *pos += 1;
            let inner = parse_unary(tokens, pos)?;
            Ok(LtlFormula::Finally(Box::new(inner)))
        }
        Token::Next => {
            *pos += 1;
            let inner = parse_unary(tokens, pos)?;
            Ok(LtlFormula::Next(Box::new(inner)))
        }
        _ => parse_primary(tokens, pos),
    }
}

/// primary → ( implies_expr ) | atom
fn parse_primary(tokens: &[Token], pos: &mut usize) -> Result<LtlFormula, String> {
    if *pos >= tokens.len() {
        return Err("Unexpected end of input".to_string());
    }
    match &tokens[*pos] {
        Token::LParen => {
            *pos += 1;
            let inner = parse_implies(tokens, pos)?;
            if *pos < tokens.len() && tokens[*pos] == Token::RParen {
                *pos += 1;
                Ok(inner)
            } else {
                Err(format!(
                    "Expected ')' at position {pos}, got {}",
                    if *pos < tokens.len() {
                        tokens[*pos].to_string()
                    } else {
                        "EOF".to_string()
                    }
                ))
            }
        }
        Token::Atom(name) => {
            let atom = LtlFormula::Atomic(name.clone());
            *pos += 1;
            Ok(atom)
        }
        other => Err(format!("Unexpected token '{other}' at position {pos}")),
    }
}

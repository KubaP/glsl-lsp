use crate::parser::{NumType, OpType};

#[derive(Debug, Clone)]
pub enum Expr {
	/// A literal value; either a number, a boolean.
	Lit(Lit),
	/// An identifier; could be a type or a variable name or...
	Ident(Ident),
	/// A negation of an expression.
	Neg(Box<Expr>),
	/// Binary expression with a left and right hand-side.
	Binary {
		left: Box<Expr>,
		op: OpType,
		right: Box<Expr>,
	},
}

#[derive(Debug, Clone)]
pub enum Stmt {
	/// An empty statement, i.e. just a `;`.
	Empty,
	/// Variable declaration.
	VarDecl {
		type_: Ident,
		ident: Ident,
		value: Expr,
	},
	/// Function declaration.
	FnDecl {
		type_: Ident,
		ident: Ident,
		body: Vec<Stmt>,
	},
}

/// A literal value.
#[derive(Debug, Clone, Copy)]
pub enum Lit {
	Bool(bool),
	Int(i64),
	UInt(u64),
	Float(f32),
	Double(f64),
}

impl std::fmt::Display for Lit {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Self::Bool(b) => write!(f, "{}", b.to_string()),
			Self::Int(i) => write!(f, "{i}"),
			Self::UInt(u) => write!(f, "{u}"),
			Self::Float(fp) => write!(f, "{fp}"),
			Self::Double(d) => write!(f, "{d}"),
		}
	}
}

impl Lit {
	pub fn parse_num(s: &str, type_: NumType) -> Result<Self, ()> {
		// Sanity check, but this should never fail.
		if s == "" {
			return Err(());
		}
		match type_ {
			NumType::Normal => Self::parse_num_dec(s),
			NumType::Hex => Self::parse_num_hex(s),
			NumType::Oct => Self::parse_num_oct(s),
			NumType::Float => Self::parse_num_float(s),
			NumType::Double => Self::parse_num_double(s),
		}
	}

	fn parse_num_dec(s: &str) -> Result<Self, ()> {
		let last = s.chars().last().unwrap();
		if last == 'u' || last == 'U' {
			// Remove the 'u' suffix.
			let s = &s[..s.len() - 1];
			if let Ok(u) = u64::from_str_radix(s, 10) {
				return Ok(Self::UInt(u));
			}
		} else {
			if let Ok(i) = i64::from_str_radix(s, 10) {
				return Ok(Self::Int(i));
			}
		}

		Err(())
	}

	fn parse_num_hex(s: &str) -> Result<Self, ()> {
		// Trim the '0x' part, otherwise the conversion will fail.
		let s = s.trim_start_matches("0x");

		let last = s.chars().last().unwrap();
		if last == 'u' || last == 'U' {
			// Remove the 'u' suffix.
			let s = &s[..s.len() - 1];
			if let Ok(u) = u64::from_str_radix(s, 16) {
				return Ok(Self::UInt(u));
			}
		} else {
			if let Ok(i) = i64::from_str_radix(s, 16) {
				return Ok(Self::Int(i));
			}
		}

		Err(())
	}

	fn parse_num_oct(s: &str) -> Result<Self, ()> {
		// Trim the '0' part, because the first '0' is not part of the number itself but rather the radix.
		let s = s.trim_start_matches("0");

		let last = s.chars().last().unwrap();
		if last == 'u' || last == 'U' {
			// Remove the 'u' suffix.
			let s = &s[..s.len() - 1];
			if let Ok(u) = u64::from_str_radix(s, 8) {
				return Ok(Self::UInt(u));
			}
		} else {
			if let Ok(i) = i64::from_str_radix(s, 8) {
				return Ok(Self::Int(i));
			}
		}

		Err(())
	}

	fn parse_num_float(s: &str) -> Result<Self, ()> {
		if let Ok(f) = s.parse::<f32>() {
			return Ok(Self::Float(f));
		}

		Err(())
	}

	fn parse_num_double(s: &str) -> Result<Self, ()> {
		// Remove the 'lf' suffix.
		let s = &s[..s.len() - 2];

		if let Ok(f) = s.parse::<f64>() {
			return Ok(Self::Double(f));
		}

		Err(())
	}
}

/// An identifier.
///
/// This can be a type name, variable name, function name, etc.
#[derive(Debug, Clone)]
pub struct Ident(pub String);

impl std::fmt::Display for Ident {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "{}", self.0)
	}
}

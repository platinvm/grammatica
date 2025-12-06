//! Chomsky hierarchy grammar implementations.
//!
//! This module provides complete implementations of all four levels of the Chomsky hierarchy,
//! a fundamental classification system for formal grammars introduced by Noam Chomsky in 1956.
//! The hierarchy demonstrates the relationship between grammatical restrictions and
//! computational power.
//!
//! # The Chomsky Hierarchy
//!
//! The Chomsky hierarchy consists of four nested classes of formal languages, each
//! corresponding to a different type of grammar:
//!
//! ## Type-3: Regular Grammars ([`RegularGrammar`])
//!
//! The most restrictive class. Productions have the form:
//! - A → a (terminal)
//! - A → aB (terminal followed by non-terminal)
//! - A → ε (epsilon)
//!
//! **Recognition**: Deterministic/Non-deterministic Finite Automata (DFA/NFA)
//! **Complexity**: O(n) time, O(1) space
//! **Applications**: Lexical analysis, pattern matching, regular expressions
//! **Examples**: Keywords, identifiers, numeric literals
//!
//! ## Type-2: Context-Free Grammars ([`ContextFreeGrammar`])
//!
//! Productions have a single non-terminal on the left side:
//! - A → α (where α is any sequence of terminals and non-terminals)
//!
//! **Recognition**: Pushdown Automata (PDA)
//! **Complexity**: O(n³) general, O(n) for deterministic subclasses
//! **Applications**: Programming language syntax, balanced structures
//! **Examples**: Nested parentheses, arithmetic expressions, most programming languages
//!
//! ## Type-1: Context-Sensitive Grammars ([`ContextSensitiveGrammar`])
//!
//! Productions must be non-contracting (|lhs| ≤ |rhs|):
//! - αAβ → αγβ (rewrite A to γ in context of α and β)
//!
//! **Recognition**: Linear Bounded Automata (LBA)
//! **Complexity**: PSPACE-complete
//! **Applications**: Natural language features, type systems with dependencies
//! **Examples**: Subject-verb agreement, cross-serial dependencies {aⁿbⁿcⁿ}
//!
//! ## Type-0: Unrestricted Grammars ([`UnrestrictedGrammar`])
//!
//! No restrictions on production forms except requiring at least one non-terminal
//! on the left side:
//! - α → β (arbitrary transformations, including contractions)
//!
//! **Recognition**: Turing Machine (undecidable in general)
//! **Complexity**: Recursively enumerable
//! **Applications**: Theoretical completeness, computational models
//! **Note**: Rarely used in practice due to undecidability
//!
//! # Hierarchy Relationships
//!
//! ```text
//! Type-3 ⊂ Type-2 ⊂ Type-1 ⊂ Type-0
//! (Regular) (Context-Free) (Context-Sensitive) (Unrestricted)
//!     ║            ║                ║                  ║
//!    DFA          PDA              LBA                TM
//!    O(n)        O(n³)         PSPACE-complete   Undecidable
//! ```
//!
//! Each class is strictly contained in the next, meaning there exist languages in
//! Type-k that cannot be expressed in Type-(k+1).
//!
//! # Common Types
//!
//! - [`Symbol`]: Represents either a terminal or non-terminal symbol
//! - [`Terminal`]: A terminal symbol wrapper with type safety
//!
//! # Examples
//!
//! ```
//! use grammatica::grammar::chomsky::{RegularGrammar, RegularProduction, RegularRhs};
//! use std::collections::HashSet;
//!
//! // Create a simple regular grammar for the language (ab)*
//! let grammar = RegularGrammar::new(
//!     HashSet::from(["S".to_string()]),
//!     HashSet::from(['a', 'b']),
//!     "S".to_string(),
//!     vec![
//!         RegularProduction::new(
//!             "S".to_string(),
//!             RegularRhs::Terminal('b')
//!         ),
//!         RegularProduction::new(
//!             "S".to_string(),
//!             RegularRhs::TerminalNonTerminal('a', "S".to_string())
//!         ),
//!     ]
//! );
//! ```
//!
//! # References
//!
//! - Chomsky, N. (1956). "Three models for the description of language"
//! - Hopcroft, J. E., & Ullman, J. D. (1979). "Introduction to Automata Theory,
//!   Languages, and Computation"

mod context_free;
mod context_sensitive;
mod regular;
mod symbol;
mod unrestricted;

pub use context_free::*;
pub use context_sensitive::*;
pub use regular::*;
pub use symbol::*;
pub use unrestricted::*;

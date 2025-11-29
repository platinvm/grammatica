//! Formal grammar definitions and implementations.
//!
//! This module provides data structures and algorithms for working with formal grammars,
//! which are mathematical models used to describe the syntax of formal languages.
//! Formal grammars are fundamental to:
//!
//! - **Compiler construction**: Parsing programming language syntax
//! - **Natural language processing**: Modeling linguistic structures
//! - **Protocol specification**: Defining communication formats
//! - **Theoretical computer science**: Understanding computational complexity
//!
//! # Organization
//!
//! The module is organized by grammar classification systems:
//!
//! - [`chomsky`]: Implementations of the Chomsky hierarchy (Type-0 through Type-3 grammars)

pub mod chomsky;

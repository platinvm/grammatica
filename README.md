# Grammatica

Grammatica is a Rust library for representing and transforming formal grammars. It currently implements the full Chomsky hierarchy (regular, context-free, context-sensitive, unrestricted) and is designed to be extensible toward additional paradigms such as attribute grammars, probabilistic/stochastic grammars, L-systems, and domain‑specific rewriting systems.

### Currently Implemented
- Regular grammars (Type‑3)
- Context-free grammars (Type‑2)
- Context-sensitive grammars (Type‑1)
- Unrestricted grammars (Type‑0)

### Planned Extensions
- Attribute grammars (semantic annotations)
- Probabilistic / weighted production systems
- Rewriting systems (Thue, string rewriting)
- L‑systems and growth models

## Goals

Core goals:
- Provide immutable, validated grammar representations
- Enable safe transformations between grammar classes
- Offer introspection utilities (counts, symbol sets, structural checks)
- Serve as a foundation for parsers, analyzers, and educational tooling

## Example (sketch)

```rust
use std::collections::HashSet;
use grammatica::grammar::chomsky::{RegularGrammar, RegularProduction, RegularRhs};

let g = RegularGrammar::new(
	HashSet::from(["S".to_string()]),
	HashSet::from(['a', 'b']),
	"S".to_string(),
	vec![
		RegularProduction { lhs: "S".to_string(), rhs: RegularRhs::Terminal('b') },
		RegularProduction { lhs: "S".to_string(), rhs: RegularRhs::TerminalNonTerminal('a', "S".to_string()) },
	]
).unwrap();
println!("start: {} productions: {}", g.start_symbol(), g.productions().len());
```

## Documentation

API docs will appear on [docs.rs](https://docs.rs/grammatica) after the first successful publish.

## License

Licensed under the MIT License. See `LICENSE` for details.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in the work shall be licensed under MIT without additional terms or conditions.

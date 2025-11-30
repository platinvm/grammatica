use std::{collections::HashSet, fmt};

use super::Symbol;

/// Error type for context-sensitive grammar validation.
///
/// This enum represents all possible errors that can occur when constructing
/// or validating a context-sensitive grammar (Type-1 grammar in the Chomsky hierarchy).
#[derive(Debug, Clone)]
pub enum ContextSensitiveError {
    StartSymbolNotFound { start_symbol: String },
    EmptyLhs { index: usize },
    LhsMissingNonTerminal { index: usize },
    StartSymbolInRhsWithEpsilon,
    LhsGreaterThanRhs { index: usize },
    NonTerminalNotFound { non_terminal: String },
    TerminalNotFound,
}

impl fmt::Display for ContextSensitiveError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ContextSensitiveError::StartSymbolNotFound { start_symbol } => {
                write!(
                    f,
                    "Start symbol '{}' not found in non-terminals",
                    start_symbol
                )
            }
            ContextSensitiveError::EmptyLhs { index } => {
                write!(f, "Production {} has empty left-hand side", index)
            }
            ContextSensitiveError::LhsMissingNonTerminal { index } => {
                write!(
                    f,
                    "Production {} left-hand side must contain at least one non-terminal",
                    index
                )
            }
            ContextSensitiveError::StartSymbolInRhsWithEpsilon => {
                write!(
                    f,
                    "Start symbol appears on right-hand side but has epsilon production"
                )
            }
            ContextSensitiveError::LhsGreaterThanRhs { index } => {
                write!(
                    f,
                    "Production {} violates context-sensitive constraint: |LHS| > |RHS|",
                    index
                )
            }
            ContextSensitiveError::NonTerminalNotFound { non_terminal } => {
                write!(f, "Non-terminal '{}' not found in grammar", non_terminal)
            }
            ContextSensitiveError::TerminalNotFound => {
                write!(f, "Terminal not found in grammar")
            }
        }
    }
}

impl std::error::Error for ContextSensitiveError {}

/// A context-sensitive grammar (Type-1 grammar in the Chomsky hierarchy).
///
/// Context-sensitive grammars (CSGs) are more expressive than context-free grammars
/// and correspond to context-sensitive languages, which can be recognized by linear
/// bounded automata (LBA). They allow production rules that depend on the surrounding
/// context of symbols.
///
/// # Grammar Form
///
/// Context-sensitive grammars have productions of the form:
/// - αAβ → αγβ
///
/// where A is a non-terminal, α and β are (possibly empty) strings of terminals
/// and non-terminals representing the context, and γ is a non-empty string of
/// terminals and non-terminals.
///
/// The key constraint is the **non-contracting property**: |αAβ| ≤ |αγβ|,
/// meaning productions cannot decrease the length of the string (except for
/// S → ε if S doesn't appear on any right-hand side).
///
/// # Properties
///
/// - **Recognition**: Can be recognized by linear bounded automata (LBA), which are
///   Turing machines with tape bounded by a constant multiple of input length.
///   Recognition is PSPACE-complete.
/// - **Decidability**: Membership problem is decidable but has exponential time
///   complexity in the worst case.
/// - **Closure properties**: Closed under union, concatenation, and Kleene star,
///   but NOT closed under complementation (open problem whether closed under
///   intersection).
/// - **Expressiveness**: Can express context-dependent patterns like
///   {aⁿbⁿcⁿ | n ≥ 0}, {ww | w ∈ Σ*} (string duplication), and many
///   natural language constructs requiring agreement (number, gender, case).
///
/// # Applications
///
/// - Natural language modeling (subject-verb agreement, anaphora resolution)
/// - Type systems with context-dependent rules
/// - DNA sequence analysis with context-dependent constraints
///
/// # Relationship to Other Grammar Types
///
/// - More powerful than context-free grammars (Type-2)
/// - Less powerful than unrestricted grammars (Type-0)
/// - Every context-free language is context-sensitive
/// - Not all context-sensitive languages are context-free (e.g., {aⁿbⁿcⁿ})
///
/// # Type Parameter
///
/// * `T` - The type of terminal symbols in the grammar. Must implement `Clone`, `Eq`,
///   and `Hash` to support efficient lookup and comparison operations.
#[derive(Debug, Clone)]
pub struct ContextSensitiveGrammar<T: Clone + Eq + std::hash::Hash> {
    non_terminals: HashSet<String>,
    terminals: HashSet<T>,
    start_symbol: String,
    productions: Vec<ContextSensitiveProduction<T>>,
}

/// A single production rule in a context-sensitive grammar.
///
/// Represents a rewrite rule of the form `α → β` where:
/// - α (lhs) is a sequence of symbols containing at least one non-terminal
/// - β (rhs) is a sequence of symbols
/// - The length constraint |α| ≤ |β| must hold (non-contracting), except for
///   the special case of S → ε where S is the start symbol and doesn't appear
///   in any right-hand side
///
/// # Type Parameter
///
/// * `T` - The type of terminal symbols in the production.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ContextSensitiveProduction<T: Clone + Eq + std::hash::Hash> {
    lhs: Vec<Symbol<T>>,
    rhs: Vec<Symbol<T>>,
}

impl<T: Clone + Eq + std::hash::Hash> ContextSensitiveGrammar<T> {
    /// Creates a new context-sensitive grammar with validation.
    ///
    /// This constructor performs comprehensive validation to ensure the grammar
    /// satisfies all requirements of a Type-1 (context-sensitive) grammar:
    ///
    /// 1. The start symbol must exist in the set of non-terminals
    /// 2. Production left-hand sides cannot be empty
    /// 3. Left-hand sides must contain at least one non-terminal
    /// 4. The **non-contracting property**: |lhs| ≤ |rhs| for all productions
    /// 5. Exception: S → ε is allowed only if S (start symbol) doesn't appear
    ///    in any right-hand side
    /// 6. All symbols must be defined in the grammar's alphabets
    ///
    /// # Arguments
    ///
    /// * `non_terminals` - Set of non-terminal symbols (variables)
    /// * `terminals` - Set of terminal symbols (alphabet)
    /// * `start_symbol` - The initial non-terminal for derivations
    /// * `productions` - Vector of production rules defining the grammar
    ///
    /// # Returns
    ///
    /// * `Ok(ContextSensitiveGrammar)` - A validated context-sensitive grammar
    /// * `Err(ContextSensitiveError)` - Validation error with context
    ///
    /// # Errors
    ///
    /// Returns `ContextSensitiveError` if:
    /// - Start symbol is not in the non-terminal set
    /// - Any production has an empty left-hand side
    /// - Any left-hand side lacks a non-terminal
    /// - The non-contracting property is violated (|lhs| > |rhs|)
    /// - Start symbol appears in RHS but has an epsilon production
    /// - Any symbol is not defined in the grammar
    ///
    /// # Examples
    ///
    /// ```
    /// use grammatica::grammar::chomsky::{ContextSensitiveGrammar, ContextSensitiveProduction, Symbol};
    /// use std::collections::HashSet;
    ///
    /// // Simplified context-sensitive grammar: aAb → aabb (context-dependent)
    /// let grammar = ContextSensitiveGrammar::new(
    ///     HashSet::from(["S".to_string(), "A".to_string()]),
    ///     HashSet::from(['a', 'b']),
    ///     "S".to_string(),
    ///     vec![
    ///         ContextSensitiveProduction::new(
    ///             vec![Symbol::NonTerminal("S".to_string())],
    ///             vec![Symbol::Terminal('a'), Symbol::NonTerminal("A".to_string()), Symbol::Terminal('b')]
    ///         ),
    ///         ContextSensitiveProduction::new(
    ///             vec![Symbol::Terminal('a'), Symbol::NonTerminal("A".to_string()), Symbol::Terminal('b')],
    ///             vec![Symbol::Terminal('a'), Symbol::Terminal('a'), Symbol::Terminal('b'), Symbol::Terminal('b')]
    ///         ),
    ///     ]
    /// ).unwrap();
    /// ```
    pub fn new(
        non_terminals: HashSet<String>,
        terminals: HashSet<T>,
        start_symbol: String,
        productions: Vec<ContextSensitiveProduction<T>>,
    ) -> Result<Self, ContextSensitiveError> {
        if !non_terminals.contains(&start_symbol) {
            return Err(ContextSensitiveError::StartSymbolNotFound { start_symbol });
        }
        for (i, prod) in productions.iter().enumerate() {
            if prod.lhs.is_empty() {
                return Err(ContextSensitiveError::EmptyLhs { index: i });
            }
            let has_non_terminal = prod.lhs.iter().any(|s| matches!(s, Symbol::NonTerminal(_)));
            if !has_non_terminal {
                return Err(ContextSensitiveError::LhsMissingNonTerminal { index: i });
            }
            if prod.rhs.is_empty() && prod.lhs.len() > 0 {
                if prod.lhs.len() == 1 {
                    if let Symbol::NonTerminal(nt) = &prod.lhs[0] {
                        if nt == &start_symbol {
                            for other_prod in &productions {
                                for symbol in &other_prod.rhs {
                                    if let Symbol::NonTerminal(rhs_nt) = symbol {
                                        if rhs_nt == &start_symbol {
                                            return Err(
                                                ContextSensitiveError::StartSymbolInRhsWithEpsilon,
                                            );
                                        }
                                    }
                                }
                            }
                        } else {
                            return Err(ContextSensitiveError::LhsGreaterThanRhs { index: i });
                        }
                    }
                } else {
                    return Err(ContextSensitiveError::LhsGreaterThanRhs { index: i });
                }
            } else if prod.lhs.len() > prod.rhs.len() {
                return Err(ContextSensitiveError::LhsGreaterThanRhs { index: i });
            }
            for symbol in prod.lhs.iter().chain(prod.rhs.iter()) {
                match symbol {
                    Symbol::NonTerminal(nt) => {
                        if !non_terminals.contains(nt) {
                            return Err(ContextSensitiveError::NonTerminalNotFound {
                                non_terminal: nt.clone(),
                            });
                        }
                    }
                    Symbol::Terminal(t) => {
                        if !terminals.contains(t) {
                            return Err(ContextSensitiveError::TerminalNotFound);
                        }
                    }
                }
            }
        }
        Ok(Self {
            non_terminals,
            terminals,
            start_symbol,
            productions,
        })
    }

    pub fn non_terminals(&self) -> &HashSet<String> {
        &self.non_terminals
    }
    pub fn terminals(&self) -> &HashSet<T> {
        &self.terminals
    }
    pub fn start_symbol(&self) -> &String {
        &self.start_symbol
    }
    pub fn productions(&self) -> &Vec<ContextSensitiveProduction<T>> {
        &self.productions
    }
    pub fn into_parts(
        self,
    ) -> (
        HashSet<String>,
        HashSet<T>,
        String,
        Vec<ContextSensitiveProduction<T>>,
    ) {
        (
            self.non_terminals,
            self.terminals,
            self.start_symbol,
            self.productions,
        )
    }
}

impl<T: Clone + Eq + std::hash::Hash> ContextSensitiveProduction<T> {
    pub fn new(lhs: Vec<Symbol<T>>, rhs: Vec<Symbol<T>>) -> Self {
        Self { lhs, rhs }
    }
    pub fn lhs(&self) -> &Vec<Symbol<T>> {
        &self.lhs
    }
    pub fn rhs(&self) -> &Vec<Symbol<T>> {
        &self.rhs
    }
    pub fn into_parts(self) -> (Vec<Symbol<T>>, Vec<Symbol<T>>) {
        (self.lhs, self.rhs)
    }
}

impl<T: Clone + Eq + std::hash::Hash> From<super::ContextFreeGrammar<T>>
    for ContextSensitiveGrammar<T>
{
    /// Converts a context-free grammar to a context-sensitive grammar.
    ///
    /// Every context-free grammar is a context-sensitive grammar, so this conversion
    /// always succeeds. Context-free productions A → α are converted to context-sensitive
    /// productions [NonTerminal(A)] → α.
    fn from(cfg: super::ContextFreeGrammar<T>) -> Self {
        let (non_terminals, terminals, start_symbol, cf_productions) = cfg.into_parts();
        let productions = cf_productions
            .into_iter()
            .map(|prod| ContextSensitiveProduction {
                lhs: vec![Symbol::NonTerminal(prod.lhs().clone())],
                rhs: prod.rhs().clone(),
            })
            .collect();
        ContextSensitiveGrammar {
            non_terminals,
            terminals,
            start_symbol,
            productions,
        }
    }
}

/// Error type for converting unrestricted grammar to context-sensitive grammar.
#[derive(Debug, Clone)]
pub enum ToContextSensitiveError {
    /// Production violates non-contracting property
    ContractingProduction {
        index: usize,
        lhs_len: usize,
        rhs_len: usize,
    },
    /// Start symbol appears in RHS but has epsilon production
    InvalidEpsilonProduction,
}

impl fmt::Display for ToContextSensitiveError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ToContextSensitiveError::ContractingProduction {
                index,
                lhs_len,
                rhs_len,
            } => {
                write!(
                    f,
                    "Production {} violates non-contracting property: |LHS|={} > |RHS|={}",
                    index, lhs_len, rhs_len
                )
            }
            ToContextSensitiveError::InvalidEpsilonProduction => {
                write!(f, "Start symbol appears in RHS but has epsilon production")
            }
        }
    }
}

impl std::error::Error for ToContextSensitiveError {}

impl<T: Clone + Eq + std::hash::Hash> TryFrom<super::UnrestrictedGrammar<T>>
    for ContextSensitiveGrammar<T>
{
    type Error = ToContextSensitiveError;

    /// Attempts to convert an unrestricted grammar to a context-sensitive grammar.
    ///
    /// This conversion succeeds only if the grammar satisfies the non-contracting property:
    /// for all productions α → β, |α| ≤ |β|, with the exception of S → ε where S is
    /// the start symbol and S does not appear in any right-hand side.
    ///
    /// # Errors
    ///
    /// Returns `ToContextSensitiveError` if:
    /// - Any production violates the non-contracting property
    /// - The start symbol has an epsilon production but appears in some right-hand side
    /// - The underlying context-sensitive grammar validation fails
    fn try_from(ug: super::UnrestrictedGrammar<T>) -> Result<Self, Self::Error> {
        // Check for epsilon productions on start symbol
        let has_start_epsilon = ug.productions().iter().any(|prod| {
            prod.lhs().len() == 1
                && matches!(&prod.lhs()[0], Symbol::NonTerminal(nt) if nt == ug.start_symbol())
                && prod.rhs().is_empty()
        });

        if has_start_epsilon {
            // Check if start symbol appears in any RHS
            for prod in ug.productions().iter() {
                if prod
                    .rhs()
                    .iter()
                    .any(|s| matches!(s, Symbol::NonTerminal(nt) if nt == ug.start_symbol()))
                {
                    return Err(ToContextSensitiveError::InvalidEpsilonProduction);
                }
            }
        }

        // Check non-contracting property for all productions
        for (i, prod) in ug.productions().iter().enumerate() {
            // Allow S → ε if S doesn't appear in RHS (already checked above)
            let is_valid_epsilon = prod.rhs().is_empty()
                && prod.lhs().len() == 1
                && matches!(&prod.lhs()[0], Symbol::NonTerminal(nt) if nt == ug.start_symbol())
                && has_start_epsilon;

            if !is_valid_epsilon && prod.lhs().len() > prod.rhs().len() {
                return Err(ToContextSensitiveError::ContractingProduction {
                    index: i,
                    lhs_len: prod.lhs().len(),
                    rhs_len: prod.rhs().len(),
                });
            }
        }
        let (non_terminals, terminals, start_symbol, unrestricted_productions) = ug.into_parts();
        let productions = unrestricted_productions
            .iter()
            .map(|prod| ContextSensitiveProduction {
                lhs: prod.lhs().clone(),
                rhs: prod.rhs().clone(),
            })
            .collect();
        ContextSensitiveGrammar::new(non_terminals, terminals, start_symbol, productions).map_err(
            |_| ToContextSensitiveError::ContractingProduction {
                index: 0,
                lhs_len: 0,
                rhs_len: 0,
            },
        )
    }
}

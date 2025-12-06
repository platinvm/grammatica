use std::{collections::HashSet, fmt};

use super::Symbol;

/// Error type for context-free grammar validation.
///
/// This enum represents all possible errors that can occur when constructing
/// or validating a context-free grammar (Type-2 grammar in the Chomsky hierarchy).
#[derive(Debug, Clone)]
pub enum ContextFreeError {
    StartSymbolNotFound { start_symbol: String },
    InvalidNonTerminalLhs { index: usize, lhs: String },
    NonTerminalNotFound { non_terminal: String },
    TerminalNotFound { index: usize },
}

impl fmt::Display for ContextFreeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ContextFreeError::StartSymbolNotFound { start_symbol } => {
                write!(
                    f,
                    "Start symbol '{}' not found in non-terminals",
                    start_symbol
                )
            }
            ContextFreeError::InvalidNonTerminalLhs { index, lhs } => {
                write!(
                    f,
                    "Production {} has invalid non-terminal '{}' on left-hand side",
                    index, lhs
                )
            }
            ContextFreeError::NonTerminalNotFound { non_terminal } => {
                write!(f, "Non-terminal '{}' not found in grammar", non_terminal)
            }
            ContextFreeError::TerminalNotFound { index: _ } => {
                write!(f, "Terminal not found in grammar")
            }
        }
    }
}

impl std::error::Error for ContextFreeError {}

/// A context-free grammar (Type-2 grammar in the Chomsky hierarchy).
///
/// Context-free grammars (CFGs) are more expressive than regular grammars and form
/// the theoretical foundation for most programming language syntax. They correspond
/// to context-free languages, which can be recognized by pushdown automata.
///
/// # Grammar Form
///
/// Context-free grammars have productions of the form:
/// - A → α
///
/// where A is a single non-terminal and α is any sequence of terminals and
/// non-terminals (including the empty string ε).
///
/// # Properties
///
/// - **Recognition**: Can be recognized by pushdown automata (PDA) or parsed using
///   algorithms like CYK, Earley, or LL/LR parsing in polynomial time O(n³) or
///   linear time O(n) for deterministic subclasses.
/// - **Closure properties**: Closed under union, concatenation, and Kleene star,
///   but NOT closed under intersection or complementation.
/// - **Expressiveness**: Can express nested structures (e.g., balanced parentheses,
///   {aⁿbⁿ | n ≥ 0}) but cannot handle context-dependent patterns like
///   {aⁿbⁿcⁿ | n ≥ 0}.
/// - **Applications**: Used extensively in:
///   * Programming language syntax (most languages are context-free)
///   * Natural language processing
///   * Markup languages (HTML, XML)
///   * Protocol specifications
///
/// # Normal Forms
///
/// CFGs can be converted to special forms:
/// - **Chomsky Normal Form (CNF)**: A → BC or A → a
/// - **Greibach Normal Form (GNF)**: A → aα where α is a string of non-terminals
///
/// # Type Parameter
///
/// * `T` - The type of terminal symbols in the grammar. Must implement `Clone`, `Eq`,
///   and `Hash` to support efficient lookup and comparison operations.
#[derive(Debug, Clone)]
pub struct ContextFreeGrammar<T: Clone + Eq + std::hash::Hash> {
    non_terminals: HashSet<String>,
    terminals: HashSet<T>,
    start_symbol: String,
    productions: Vec<ContextFreeProduction<T>>,
}

/// A single production rule in a context-free grammar.
///
/// Represents a rewrite rule of the form `A → α` where A is a single non-terminal
/// symbol (the left-hand side must be exactly one non-terminal) and α is any
/// sequence of terminals and non-terminals on the right-hand side.
///
/// This is the defining characteristic of context-free grammars: the left-hand side
/// is always a single non-terminal, independent of any surrounding context.
///
/// # Type Parameter
///
/// * `T` - The type of terminal symbols in the production.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ContextFreeProduction<T: Clone + Eq + std::hash::Hash> {
    lhs: String,
    rhs: Vec<Symbol<T>>,
}

impl<T: Clone + Eq + std::hash::Hash> ContextFreeGrammar<T> {
    /// Creates a new context-free grammar with validation.
    ///
    /// This constructor performs comprehensive validation to ensure the grammar
    /// satisfies all requirements of a Type-2 (context-free) grammar:
    ///
    /// 1. The start symbol must exist in the set of non-terminals
    /// 2. All production left-hand sides must be single, valid non-terminals
    /// 3. All symbols in right-hand sides must be defined in the grammar
    /// 4. All terminals and non-terminals must be properly declared
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
    /// * `Ok(ContextFreeGrammar)` - A validated context-free grammar
    /// * `Err(ContextFreeError)` - Validation error with context
    ///
    /// # Errors
    ///
    /// Returns `ContextFreeError` if:
    /// - Start symbol is not in the non-terminal set
    /// - Any production has an invalid left-hand side non-terminal
    /// - Any symbol in productions is not defined in the grammar
    ///
    /// # Examples
    ///
    /// ```
    /// use grammatica::grammar::chomsky::{ContextFreeGrammar, ContextFreeProduction, Symbol};
    /// use std::collections::HashSet;
    ///
    /// // Grammar for balanced parentheses: S → (S) | SS | ε
    /// let grammar = ContextFreeGrammar::new(
    ///     HashSet::from(["S".to_string()]),
    ///     HashSet::from(['(', ')']),
    ///     "S".to_string(),
    ///     vec![
    ///         ContextFreeProduction::new(
    ///             "S".to_string(),
    ///             vec![Symbol::Terminal('('), Symbol::NonTerminal("S".to_string()), Symbol::Terminal(')')]
    ///         ),
    ///         ContextFreeProduction::new(
    ///             "S".to_string(),
    ///             vec![Symbol::NonTerminal("S".to_string()), Symbol::NonTerminal("S".to_string())]
    ///         ),
    ///         ContextFreeProduction::new(
    ///             "S".to_string(),
    ///             vec![] // epsilon
    ///         ),
    ///     ]
    /// ).unwrap();
    /// ```
    pub fn new(
        non_terminals: HashSet<String>,
        terminals: HashSet<T>,
        start_symbol: String,
        productions: Vec<ContextFreeProduction<T>>,
    ) -> Result<Self, ContextFreeError> {
        if !non_terminals.contains(&start_symbol) {
            return Err(ContextFreeError::StartSymbolNotFound { start_symbol });
        }
        for (i, prod) in productions.iter().enumerate() {
            if !non_terminals.contains(&prod.lhs) {
                return Err(ContextFreeError::InvalidNonTerminalLhs {
                    index: i,
                    lhs: prod.lhs.clone(),
                });
            }
            for symbol in &prod.rhs {
                match symbol {
                    Symbol::NonTerminal(nt) => {
                        if !non_terminals.contains(nt) {
                            return Err(ContextFreeError::NonTerminalNotFound {
                                non_terminal: nt.clone(),
                            });
                        }
                    }
                    Symbol::Terminal(t) => {
                        if !terminals.contains(t) {
                            return Err(ContextFreeError::TerminalNotFound { index: i });
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
    pub fn productions(&self) -> &Vec<ContextFreeProduction<T>> {
        &self.productions
    }
    pub fn into_parts(
        self,
    ) -> (
        HashSet<String>,
        HashSet<T>,
        String,
        Vec<ContextFreeProduction<T>>,
    ) {
        (
            self.non_terminals,
            self.terminals,
            self.start_symbol,
            self.productions,
        )
    }
}

impl<T: Clone + Eq + std::hash::Hash> ContextFreeProduction<T> {
    pub fn new(lhs: String, rhs: Vec<Symbol<T>>) -> Self {
        Self { lhs, rhs }
    }
    pub fn lhs(&self) -> &String {
        &self.lhs
    }
    pub fn rhs(&self) -> &Vec<Symbol<T>> {
        &self.rhs
    }
    pub fn into_parts(self) -> (String, Vec<Symbol<T>>) {
        (self.lhs, self.rhs)
    }
}

impl<T: Clone + Eq + std::hash::Hash> From<super::RegularGrammar<T>> for ContextFreeGrammar<T> {
    /// Converts a regular grammar to a context-free grammar.
    ///
    /// Every regular grammar is a context-free grammar, so this conversion always succeeds.
    /// Regular productions are converted to context-free productions:
    /// - A → a becomes A → [Terminal(a)]
    /// - A → aB becomes A → [Terminal(a), NonTerminal(B)]
    /// - A → ε becomes A → []
    fn from(rg: super::RegularGrammar<T>) -> Self {
        let (non_terminals, terminals, start_symbol, regular_productions) = rg.into_parts();
        let productions = regular_productions
            .into_iter()
            .map(|prod| {
                let rhs = match prod.rhs() {
                    super::RegularRhs::Terminal(t) => vec![Symbol::Terminal(t.clone())],
                    super::RegularRhs::TerminalNonTerminal(t, nt) => {
                        vec![Symbol::Terminal(t.clone()), Symbol::NonTerminal(nt.clone())]
                    }
                    super::RegularRhs::Epsilon => vec![],
                };
                let lhs = prod.lhs().clone();
                ContextFreeProduction { lhs, rhs }
            })
            .collect();
        ContextFreeGrammar {
            non_terminals,
            terminals,
            start_symbol,
            productions,
        }
    }
}

/// Error type for converting context-sensitive grammar to context-free grammar.
#[derive(Debug, Clone)]
pub enum ToContextFreeError {
    /// Production has invalid form for context-free grammar
    InvalidProductionForm { index: usize, reason: String },
}

impl fmt::Display for ToContextFreeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ToContextFreeError::InvalidProductionForm { index, reason } => {
                write!(
                    f,
                    "Production {} cannot be converted to context-free form: {}",
                    index, reason
                )
            }
        }
    }
}

impl std::error::Error for ToContextFreeError {}

impl<T: Clone + Eq + std::hash::Hash> TryFrom<super::ContextSensitiveGrammar<T>>
    for ContextFreeGrammar<T>
{
    type Error = ToContextFreeError;

    /// Attempts to convert a context-sensitive grammar to a context-free grammar.
    ///
    /// This conversion succeeds only if all productions have a single non-terminal
    /// on the left-hand side, which is the defining constraint of context-free grammars.
    ///
    /// # Errors
    ///
    /// Returns `ToContextFreeError` if any production has a left-hand side that is not
    /// a single non-terminal, or if the underlying context-free grammar validation fails.
    fn try_from(csg: super::ContextSensitiveGrammar<T>) -> Result<Self, Self::Error> {
        let mut cf_productions = Vec::new();

        for (i, prod) in csg.productions().iter().enumerate() {
            // Context-free grammars require exactly one non-terminal on the LHS
            if prod.lhs().len() != 1 {
                return Err(ToContextFreeError::InvalidProductionForm {
                    index: i,
                    reason: format!(
                        "left-hand side must be a single symbol, found {}",
                        prod.lhs().len()
                    ),
                });
            }

            let lhs = match &prod.lhs()[0] {
                Symbol::NonTerminal(nt) => nt.clone(),
                Symbol::Terminal(_) => {
                    return Err(ToContextFreeError::InvalidProductionForm {
                        index: i,
                        reason: "left-hand side must be a non-terminal".to_string(),
                    });
                }
            };

            cf_productions.push(ContextFreeProduction {
                lhs,
                rhs: prod.rhs().clone(),
            });
        }
        let (non_terminals, terminals, start_symbol, _) = csg.into_parts();
        ContextFreeGrammar::new(non_terminals, terminals, start_symbol, cf_productions).map_err(
            |e| ToContextFreeError::InvalidProductionForm {
                index: 0,
                reason: e.to_string(),
            },
        )
    }
}

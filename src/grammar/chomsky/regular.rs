use std::{collections::HashSet, fmt};

/// Error type for regular grammar validation.
///
/// This enum represents all possible errors that can occur when constructing
/// or validating a regular grammar (Type-3 grammar in the Chomsky hierarchy).
#[derive(Debug, Clone)]
pub enum RegularError {
    StartSymbolNotFound { start_symbol: String },
    InvalidNonTerminalLhs { index: usize, lhs: String },
    InvalidTerminal { index: usize },
    InvalidNonTerminalRhs { index: usize, non_terminal: String },
}

impl fmt::Display for RegularError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RegularError::StartSymbolNotFound { start_symbol } => {
                write!(
                    f,
                    "Start symbol '{}' not found in non-terminals",
                    start_symbol
                )
            }
            RegularError::InvalidNonTerminalLhs { index, lhs } => {
                write!(
                    f,
                    "Production {} has invalid non-terminal '{}' on left-hand side",
                    index, lhs
                )
            }
            RegularError::InvalidTerminal { index } => {
                write!(f, "Production {} has invalid terminal", index)
            }
            RegularError::InvalidNonTerminalRhs {
                index,
                non_terminal,
            } => {
                write!(
                    f,
                    "Production {} has invalid non-terminal '{}'",
                    index, non_terminal
                )
            }
        }
    }
}

impl std::error::Error for RegularError {}

/// A regular grammar (Type-3 grammar in the Chomsky hierarchy).
///
/// Regular grammars are the most restrictive class of formal grammars and correspond
/// to regular languages, which can be recognized by finite automata. In the Chomsky
/// hierarchy, Type-3 grammars are a proper subset of context-free grammars.
///
/// # Grammar Form
///
/// Regular grammars have productions of the form:
/// - A → a (terminal)
/// - A → aB (terminal followed by non-terminal, right-regular)
/// - A → ε (epsilon/empty string)
///
/// where A and B are non-terminals and a is a terminal symbol.
///
/// # Properties
///
/// - **Closure properties**: Regular languages are closed under union, concatenation,
///   Kleene star, intersection, and complementation.
/// - **Recognition**: Can be recognized by deterministic finite automata (DFA) or
///   non-deterministic finite automata (NFA) in linear time O(n).
/// - **Expressiveness**: Can express patterns with finite memory but cannot handle
///   nested structures or counting (e.g., {aⁿbⁿ | n ≥ 0} is not regular).
///
/// # Type Parameter
///
/// * `T` - The type of terminal symbols in the grammar. Must implement `Clone`, `Eq`,
///   and `Hash` to support efficient lookup and comparison operations.
#[derive(Debug, Clone)]
pub struct RegularGrammar<T: Clone + Eq + std::hash::Hash> {
    non_terminals: HashSet<String>,
    terminals: HashSet<T>,
    start_symbol: String,
    productions: Vec<RegularProduction<T>>,
}

/// A single production rule in a regular grammar.
///
/// Represents a rewrite rule of the form `A → α` where A is a non-terminal
/// symbol and α is a regular right-hand side (terminal, terminal+non-terminal,
/// or epsilon).
///
/// # Type Parameter
///
/// * `T` - The type of terminal symbols in the production.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RegularProduction<T: Clone + Eq + std::hash::Hash> {
    lhs: String,
    rhs: RegularRhs<T>,
}

/// The right-hand side of a regular production.
///
/// Regular grammars restrict the form of production rules to three possible types,
/// which collectively define the structure of regular (Type-3) languages.
///
/// # Variants
///
/// * `Terminal(T)` - A single terminal symbol (A → a)
/// * `TerminalNonTerminal(T, String)` - A terminal followed by a non-terminal (A → aB),
///   representing right-regular form
/// * `Epsilon` - The empty string (A → ε), allowing optional elements
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum RegularRhs<T: Clone + Eq + std::hash::Hash> {
    Terminal(T),
    TerminalNonTerminal(T, String),
    Epsilon,
}

impl<T: Clone + Eq + std::hash::Hash> RegularGrammar<T> {
    /// Creates a new regular grammar with validation.
    ///
    /// This constructor performs comprehensive validation to ensure the grammar
    /// satisfies all requirements of a Type-3 (regular) grammar:
    ///
    /// 1. The start symbol must exist in the set of non-terminals
    /// 2. All production left-hand sides must be valid non-terminals
    /// 3. All terminals in productions must exist in the terminal set
    /// 4. All non-terminals in productions must exist in the non-terminal set
    ///
    /// # Arguments
    ///
    /// * `non_terminals` - Set of non-terminal symbols (typically uppercase letters)
    /// * `terminals` - Set of terminal symbols (alphabet of the language)
    /// * `start_symbol` - The initial non-terminal for derivations
    /// * `productions` - Vector of production rules defining the grammar
    ///
    /// # Returns
    ///
    /// * `Ok(RegularGrammar)` - A validated regular grammar
    /// * `Err(RegularError)` - Validation error with context about what went wrong
    ///
    /// # Errors
    ///
    /// Returns `RegularError` if:
    /// - Start symbol is not in the non-terminal set
    /// - Any production references undefined non-terminals or terminals
    ///
    /// # Examples
    ///
    /// ```
    /// use grammatica::grammar::chomsky::{RegularGrammar, RegularProduction, RegularRhs};
    /// use std::collections::HashSet;
    ///
    /// // Grammar for the language a*b (zero or more a's followed by b)
    /// let grammar = RegularGrammar::new(
    ///     HashSet::from(["S".to_string()]),
    ///     HashSet::from(['a', 'b']),
    ///     "S".to_string(),
    ///     vec![
    ///         RegularProduction::new("S".to_string(), RegularRhs::Terminal('b')),
    ///         RegularProduction::new("S".to_string(), RegularRhs::TerminalNonTerminal('a', "S".to_string())),
    ///     ]
    /// ).unwrap();
    /// ```
    pub fn new(
        non_terminals: HashSet<String>,
        terminals: HashSet<T>,
        start_symbol: String,
        productions: Vec<RegularProduction<T>>,
    ) -> Result<Self, RegularError> {
        if !non_terminals.contains(&start_symbol) {
            return Err(RegularError::StartSymbolNotFound { start_symbol });
        }
        for (i, prod) in productions.iter().enumerate() {
            if !non_terminals.contains(&prod.lhs) {
                return Err(RegularError::InvalidNonTerminalLhs {
                    index: i,
                    lhs: prod.lhs.clone(),
                });
            }
            match &prod.rhs {
                RegularRhs::Terminal(t) => {
                    if !terminals.contains(t) {
                        return Err(RegularError::InvalidTerminal { index: i });
                    }
                }
                RegularRhs::TerminalNonTerminal(t, nt) => {
                    if !terminals.contains(t) {
                        return Err(RegularError::InvalidTerminal { index: i });
                    }
                    if !non_terminals.contains(nt) {
                        return Err(RegularError::InvalidNonTerminalRhs {
                            index: i,
                            non_terminal: nt.clone(),
                        });
                    }
                }
                RegularRhs::Epsilon => {}
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
    pub fn productions(&self) -> &Vec<RegularProduction<T>> {
        &self.productions
    }
    pub fn into_parts(
        self,
    ) -> (
        HashSet<String>,
        HashSet<T>,
        String,
        Vec<RegularProduction<T>>,
    ) {
        (
            self.non_terminals,
            self.terminals,
            self.start_symbol,
            self.productions,
        )
    }
}

impl<T: Clone + Eq + std::hash::Hash> RegularProduction<T> {
    pub fn new(lhs: String, rhs: RegularRhs<T>) -> Self {
        Self { lhs, rhs }
    }
    pub fn lhs(&self) -> &String {
        &self.lhs
    }
    pub fn rhs(&self) -> &RegularRhs<T> {
        &self.rhs
    }
    pub fn into_parts(self) -> (String, RegularRhs<T>) {
        (self.lhs, self.rhs)
    }
}

/// Error type for converting context-free grammar to regular grammar.
#[derive(Debug, Clone)]
pub enum ToRegularError {
    /// Production has invalid form for regular grammar
    InvalidProductionForm { index: usize, reason: String },
}

impl fmt::Display for ToRegularError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ToRegularError::InvalidProductionForm { index, reason } => {
                write!(
                    f,
                    "Production {} cannot be converted to regular form: {}",
                    index, reason
                )
            }
        }
    }
}

impl std::error::Error for ToRegularError {}

impl<T: Clone + Eq + std::hash::Hash> TryFrom<super::ContextFreeGrammar<T>> for RegularGrammar<T> {
    type Error = ToRegularError;

    /// Attempts to convert a context-free grammar to a regular grammar.
    ///
    /// This conversion succeeds only if all productions are in regular form:
    /// - A → a (single terminal)
    /// - A → aB (terminal followed by non-terminal)
    /// - A → ε (epsilon)
    ///
    /// # Errors
    ///
    /// Returns `ToRegularError` if any production violates regular grammar constraints,
    /// or if the underlying regular grammar validation fails.
    fn try_from(cfg: super::ContextFreeGrammar<T>) -> Result<Self, Self::Error> {
        let mut regular_productions = Vec::new();

        for (i, prod) in cfg.productions().iter().enumerate() {
            let rhs = match prod.rhs().as_slice() {
                [] => RegularRhs::Epsilon,
                [super::Symbol::Terminal(t)] => RegularRhs::Terminal(t.clone()),
                [super::Symbol::Terminal(t), super::Symbol::NonTerminal(nt)] => {
                    RegularRhs::TerminalNonTerminal(t.clone(), nt.clone())
                }
                _ => {
                    return Err(ToRegularError::InvalidProductionForm {
                        index: i,
                        reason: "right-hand side must be: ε, terminal, or terminal+non-terminal"
                            .to_string(),
                    });
                }
            };
            regular_productions.push(RegularProduction {
                lhs: prod.lhs().clone(),
                rhs,
            });
        }

        let (non_terminals, terminals, start_symbol, _) = cfg.into_parts();
        RegularGrammar::new(non_terminals, terminals, start_symbol, regular_productions).map_err(
            |e| ToRegularError::InvalidProductionForm {
                index: 0,
                reason: e.to_string(),
            },
        )
    }
}

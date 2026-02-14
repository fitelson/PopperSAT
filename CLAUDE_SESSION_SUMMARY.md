# PopperSAT Development Session Summary

**Date**: 2026-01-30 (updated after Session 8)
**Purpose**: Converting PrSAT (Kolmogorov probability satisfiability checker) to PopperSAT (Popper function satisfiability checker)

> **Important**: Do not use git commands in this project. This is local code that is manually uploaded to fitelson.org. The original PrSAT codebase is from imapersonman/PrSAT but this fork (PopperSAT) is maintained separately.

## Background

PrSAT 3.0 is a decision procedure for checking satisfiability of constraints on Kolmogorov probability functions. The user (Branden Fitelson) wants to extend it to handle **Popper functions** — where probability is fundamentally a two-place function P(A | B), not derived from a one-place function.

### Key Difference: Popper vs Kolmogorov

- **Kolmogorov**: P(A) is primitive; P(A|B) = P(A∧B)/P(B) is derived (undefined when P(B)=0)
- **Popper**: P(A|B) is primitive; conditioning on zero-probability events is allowed
  - If ψ is **normal** (positive probability at some layer): standard conditional probability
  - If ψ is **abnormal** (zero probability at all layers): P(φ|ψ) = 1 for ALL φ

### Proposed Algorithm (from user's PDF)

Use **Lexicographic Probability Systems (LPS)**:
- Multiple layers of probability measures (μ₁, ..., μ_K)
- For P(φ|ψ): find first layer where ψ has positive mass, compute ratio there
- Outer search over "layer assignments" for conditioning events
- Inner QF_NRA Z3 calls for each assignment
- Division-free encoding: use `n = p · d` instead of `p = n/d`

## Changes Made This Session

### 1. Syntax: Removed Bare Pr(A)

All probability expressions must now be conditional `Pr(A | B)`. Bare `Pr(A)` returns a helpful error directing users to write `Pr(A | ⊤)`.

**Files changed**: `types.ts`, `pr_sat.ts`, `parser.ts`, `prsat_to_html.ts`, `z3_integration.ts`, various test files

### 2. New File: `src/popper.ts`

Utilities for the Popper conditional probability table:

```typescript
// Key exports:
generateAllPropositions(tt: TruthTable): Proposition[]  // All 2^(2^n) propositions
propositionLabel(tt, prop, index): string               // Returns p₁, p₂, etc.
propositionDNF(tt, prop): string                        // Human-readable DNF
createStubPopperModel(tt): PopperModel                  // Placeholder (uniform dist)
computeConditionalProbabilityTable(tt, model, props): number[][]

// Types:
type Proposition = Set<number>  // Set of state indices where prop is true
type PopperModel = {
  isAbnormal: (prop: Proposition) => boolean
  conditionalProbability: (phi: Proposition, psi: Proposition) => number | undefined
}
```

### 3. UI Changes in `src/text_to_display.ts`

- Removed translated constraints display (internal encoding too complex)
- Removed "Save translated constraints" and "Save SMTLIB input" buttons
- Added `popper_model_display()` for the 2^(2^n) × 2^(2^n) table
- **Table is optional** — hidden by default with checkbox to show
- Model evaluator remains primary interface for querying values

### 4. Output Format

When SAT: Shows message about model found, optional table toggle, evaluator for queries

Table features (when shown):
- Propositions labeled p₁, p₂, ... with subscript digits
- Color coding: green (1, normal), gray (1, abnormal), red (0)
- Collapsible DNF legend showing what each pᵢ means
- Tooltips with full details

## Completed This Session

1. **✓ Replaced PrSAT Solver with LPS Solver**
   - `start_search_solver` now calls `solveLPS()` instead of `pr_sat_wrapped()`
   - Added `PopperSATResult` type that includes `popperModel` and `lpsResult`
   - `lpsModelToPopperModel()` converts LPS output to display format
   - Removed unused `pr_sat_wrapped` import

2. **✓ Model Evaluator Integration**
   - Model evaluator now uses Popper model for evaluation
   - Added `sentenceToProposition()` to convert sentences to propositions
   - Added `evaluateWithPopperModel()` for evaluating constraints/real expressions
   - Handles free variable checking and division-by-zero errors

3. **✓ Multi-Layer Abnormality Handling**
   - LPS solver now extracts actual layer variable values from Z3 model
   - Added `model_to_named_assignments()` to extract values by variable name
   - Abnormality computed properly: zero mass at ALL layers
   - Properly parses `a_k_s` format layer variables

4. **✓ Popper-Specific Test Suite**
   - Created `src/popper.spec.ts` with 19 tests
   - Tests cover: proposition utilities, LPS solver, Popper model evaluation
   - Fixed infinite recursion bug in `extractConditioningEvents()`
   - All 564 tests pass (19 new + 545 original)

## Session 2 Changes

1. **Fixed: Conditional Probability Table Bug**
   - Table was showing all 1's due to using empty `state_assignments` instead of the LPS model
   - Fixed by using `state.solver_output.popperModel!` directly

2. **Added: Popper Axiom Verification**
   - New `verifyPopperAxioms()` function checks all 6 Popper axioms
   - UI checkbox to run verification with pass/fail display
   - Note: O(n³) complexity — slow for 3+ atomic sentences

3. **Changed: Fractions Instead of Decimals**
   - Evaluator now shows fractions (3/4) instead of decimals (0.75)
   - Uses MathML `<mfrac>` for proper rendering
   - Supports denominators: 2-10, 12, 15, 16, 18, 20, 24, 25

4. **Removed: Flash of Old PrSAT Table**
   - Deleted `truth_table_display()` function that briefly showed during search

5. **Verified: Abnormal Event Semantics**
   - Law of total probability correctly "fails" for abnormal B (returns 2, not 1)
   - This is correct! Popper's additivity only applies to normal events
   - To test for normal B, add `Pr(f | B) = 0`

## Session 3 Changes

1. **Added: Exact Rational Arithmetic**
   - Probability table now shows exact fractions (e.g., `24/31`) instead of decimals
   - New `ExactNumber` type: either `Rational` (exact) or `float` (for irrationals)
   - `Rational` uses `bigint` for arbitrary precision: `{numer: bigint, denom: bigint}`
   - Arithmetic stays rational when both operands are rational

2. **Updated: Z3 Model Extraction**
   - New `model_to_named_assignments_exact()` extracts exact rationals from Z3
   - Fixed parsing of Z3's `(/ 1.0 4.0)` format (decimals instead of integers)
   - Falls back to float only for unparseable expressions (e.g., `root-obj` for irrationals)

3. **Updated: LPS Solver**
   - `layerValues` now stores `ExactNumber` instead of `number`
   - `conditionalProbabilityExact` computes P(φ|ψ) using exact rational division
   - `LPSModel` type updated with new field

4. **Updated: Display**
   - `popper_model_display` uses `conditionalProbabilityExact` when available
   - Fractions displayed directly without guessing denominators
   - Decimals only appear for genuinely irrational values

5. **Added: Model Evaluator Exact Numbers**
   - New `evaluateRealExprExact()` function in popper.ts for exact rational evaluation
   - New `evaluateWithPopperModelExact()` for full constraint/expression exact evaluation
   - Model evaluator now returns exact fractions when querying probabilities
   - Queries like `Pr(A | t)` show `1/4` instead of `0.25`

6. **Added: Exact Algebraic Numbers (Quadratic Surds)**
   - New `QuadraticSurd` type: `{a: Rational, b: Rational, c: bigint}` representing `a + b√c`
   - Extended `ExactNumber` to include `'surd'` tag
   - Surd arithmetic preserves exactness when same radicand
   - Z3's `root-obj` quadratic expressions parsed as exact surds
   - Model evaluator displays surds like `(-3 + √17)/8` with MathML
   - Table display unchanged (decimals for irrationals)

**Key Types Added:**
```typescript
type Rational = { numer: bigint, denom: bigint }
type QuadraticSurd = { a: Rational, b: Rational, c: bigint }  // a + b√c
type ExactNumber =
  | { tag: 'rational', value: Rational }
  | { tag: 'surd', value: QuadraticSurd }
  | { tag: 'float', value: number }
```

## Session 4 Changes

1. **Fixed: Table Showing Decimals for Rationals**
   - Was converting exact rationals to floats, then guessing fractions (limited denominators)
   - Now uses exact rational directly when available
   - **Table**: Exact fractions for rationals, decimals only for irrationals
   - **Evaluator**: Exact numbers (fractions, surds like `(-3 + √17)/8`)
   - Tooltip always shows exact value

2. **Changed: Proposition Display Symbols**
   - Negation: `~` (was `¬`)
   - Conjunction: `&` (was `∧`)
   - Disjunction: `∨` (unchanged)
   - Example: `A&~B` instead of `A∧¬B`

**Files changed:** `src/popper.ts` (stateLabel, propositionDNF functions)

## Session 8 Changes

1. **Improved: MathML Support Error Message**
   - Error message now explains what MathML is needed for
   - Lists specific browser version requirements (Chrome 109+, Firefox, Safari, Edge 109+)
   - Tells users to update their browser

**Files changed:** `src/text_to_display.ts`

## Session 7 Changes

1. **Changed: Title to "PopperSAT 1.0b"**
   - Updated main header title from "PopperSAT" to "PopperSAT 1.0b"
   - Updated HTML page title (browser tab) to match

2. **Added: Beta Notice with Bug Report Link**
   - Added fourth line to subtitle: "This is a beta version. Please report any bugs to Branden Fitelson."
   - "Branden Fitelson" links to http://fitelson.org/

**Files changed:** `src/text_to_display.ts`, `index.html`

## Session 6 Changes

1. **Changed: Updated Subtitle Text**
   - Added introductory line: "PopperSAT is a decision procedure for Popper functions."
   - Three-line subtitle now reads:
     - Line 1: PopperSAT is a decision procedure for Popper functions.
     - Line 2: It uses the same syntax as PrSAT, except unconditional probabilities "Pr(X)" are not allowed.
     - Line 3: Instead, use "Pr(X | t)", where "t" is a constant symbol representing an arbitrary tautology.
   - "PrSAT" remains a hyperlink to http://fitelson.org/PrSAT/

**Files changed:** `src/text_to_display.ts`

## Session 5 Changes

1. **Added: Subtitle Explaining Syntax Difference from PrSAT**
   - Two-line explanatory text below the "PopperSAT" title
   - Explains that `Pr(X)` is not allowed; must use `Pr(X | t)`
   - "PrSAT" is a hyperlink to http://fitelson.org/PrSAT/
   - White text to match header styling

2. **Changed: Conditional UI Button Display Based on Problem Size**
   - Buttons now shown based on number of atomic sentences (n):
     - **n ≤ 2**: Both "Show table" and "Verify axioms" buttons
     - **n = 3**: Only "Show table" button (axiom verification too slow)
     - **n ≥ 4**: Neither button (table too large to be useful)
   - Uses `truth_table.n_letters()` to determine n

**Files changed:** `src/text_to_display.ts`

## What Still Needs To Be Done

1. **Optimization** (optional)
   - Layer assignment search pruning
   - Performance improvements for large constraint sets

## File Structure

```
src/
  popper.ts          # Popper utilities: propositions, table, axiom verification, evaluation
  lps_solver.ts      # LPS solver: SMTLIB generation, layer assignments, model building (uses ExactNumber)
  types.ts           # Modified: removed 'probability' type
  pr_sat.ts          # Modified: removed pr() builder
  parser.ts          # Modified: Pr(A) now errors
  text_to_display.ts # UI: table display, axiom verification UI, exact fraction formatting
  z3_integration.ts  # Rational/ExactNumber types, exact arithmetic, Z3 model extraction
  prsat_to_html.ts   # Modified: removed probability case
```

## LPS Solver Architecture (lps_solver.ts)

The solver works by:
1. Extract conditioning events from constraints
2. Generate layer assignments (which layer each event belongs to)
3. For each assignment, generate SMTLIB with division-free encoding
4. Call Z3 and return first SAT result

**Status**: Fully integrated into UI via `start_search_solver`.

Key types:
- `LayerAssignment`: Map from proposition key to layer number (0 = abnormal)
- `LPSModel`: Contains layer values and conditionalProbability function
- `Proposition`: Set<number> of state indices

Division-free encoding: Instead of `p = n/d`, we use:
```
(declare-const _p0 Real)      ; fresh variable for P(φ|ψ)
(assert (>= _p0 0))
(assert (<= _p0 1))
(assert (= numerator (* _p0 denominator)))
```

## Testing

All tests pass: 564 passed, 23 skipped (19 Popper-specific tests added in Session 1).

## Key Popper Semantics to Remember

For the conditional probability table P(φ | ψ):

| Condition | Value |
|-----------|-------|
| ψ is abnormal | 1 (for all φ) |
| ψ is normal, ψ ⊆ φ (ψ entails φ) | 1 |
| ψ is normal, ψ ∩ φ = ∅ (mutually exclusive) | 0 |
| ψ is normal, otherwise | computed from model |

⊥ (contradiction) is always abnormal. ⊤ (tautology) is always normal at layer 1.

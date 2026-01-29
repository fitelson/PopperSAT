# PopperSAT Development Session Summary

**Date**: 2026-01-29
**Purpose**: Converting PrSAT (Kolmogorov probability satisfiability checker) to PopperSAT (Popper function satisfiability checker)

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

## What Still Needs To Be Done

1. **Optimization** (optional)
   - Layer assignment search pruning
   - Performance improvements for large constraint sets

## File Structure

```
src/
  popper.ts          # NEW: Popper-specific utilities (propositions, table generation)
  lps_solver.ts      # NEW: LPS solver infrastructure (SMTLIB generation, layer assignments)
  types.ts           # Modified: removed 'probability' type
  pr_sat.ts          # Modified: removed pr() builder
  parser.ts          # Modified: Pr(A) now errors
  text_to_display.ts # Modified: new table display, removed old display
  z3_integration.ts  # Modified: removed probability case
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

All tests pass: 545 passed, 23 skipped. The test suite takes ~33 seconds to run.

## Key Popper Semantics to Remember

For the conditional probability table P(φ | ψ):

| Condition | Value |
|-----------|-------|
| ψ is abnormal | 1 (for all φ) |
| ψ is normal, ψ ⊆ φ (ψ entails φ) | 1 |
| ψ is normal, ψ ∩ φ = ∅ (mutually exclusive) | 0 |
| ψ is normal, otherwise | computed from model |

⊥ (contradiction) is always abnormal. ⊤ (tautology) is always normal at layer 1.

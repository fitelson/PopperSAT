# PrSAT 3.0 Changelog

> **Note:** This is a local build for deployment to fitelson.org. These changes are not committed to the GitHub repository (imapersonman/PrSAT).

## 2026-01-29

### Changed: Probability Now Requires Conditioning Event (PopperSAT Foundation)

- Bare probability terms `Pr(A)` are no longer allowed in the syntax
- All probability expressions must now be conditional: `Pr(A | B)`
- To express unconditional probability, write `Pr(A | ⊤)` (probability of A given tautology)
- Parser now returns a helpful error message when bare `Pr(A)` is entered

**Rationale:** This change prepares the codebase for PopperSAT, where probability is fundamentally a two-place function P(A | B) following Popper's axiomatization. In Popper's system, `Pr(A)` is not well-formed — it must be written as `Pr(A | ⊤)`.

**Changes:**
- `src/types.ts`: Removed `probability` type variant from `RealExpr`; only `given_probability` remains
- `src/pr_sat.ts`: Removed `pr` builder and all `probability` case handling throughout
- `src/parser.ts`: Changed bare `Pr(A)` to return error: "Popper probability requires a conditioning event. Write Pr(A | ⊤) instead of Pr(A)"
- `src/parser.spec.ts`: Updated tests to use conditional form; added error test for bare `Pr(A)`
- `src/prsat_to_html.ts`: Removed `probability` case from HTML rendering
- `src/z3_integration.ts`: Removed `probability` case from Z3 translation
- `src/example.spec.ts`, `src/pr_sat.spec.ts`, `src/tag_map.spec.ts`: Updated tests to use `given_probability`

### Changed: Output Now Shows Conditional Probability Table (Optional)

- Replaced the old state-variable assignment table with a full conditional probability table
- For n atomic sentences, table would be 2^(2^n) × 2^(2^n) — this grows very fast!
- **Table is now optional**: hidden by default, with a checkbox to show it
- Primary interface is the model evaluator, where users can query specific P(φ | ψ) values
- When shown, table features:
  - Rows are conditioning events (ψ), columns are propositions (φ)
  - Propositions labeled as p₁, p₂, ..., p_{2^(2^n)} for clarity
  - Visual indicators: green for 1 (normal), gray for 1 (abnormal), red for 0
  - Scrolling for large sizes and tooltips showing proposition DNFs
  - Collapsible "Proposition definitions (DNF)" legend shows the DNF for each pᵢ

**Popper semantics reflected in table:**
- Diagonal entries P(φ | φ) = 1 for all non-⊥ propositions
- P(φ | ψ) = 0 when φ and ψ are mutually exclusive AND ψ is normal
- P(φ | ψ) = 1 for ALL φ when ψ is abnormal (zero probability at all layers)
- ⊥ (contradiction) is always abnormal

**Changes:**
- `src/popper.ts`: New file with utilities for generating propositions, labeling, and computing conditional probability tables
  - `propositionLabel()`: Returns p₁, p₂, etc. with subscript digits
  - `propositionDNF()`: Returns human-readable DNF for the legend
- `src/text_to_display.ts`:
  - Added `popper_model_display()` function for the new table format
  - Replaced `model_display()` with `popper_model_display()` in SAT result display
  - Removed display of translated algebraic constraints (internal representation now more complex)
  - Removed "Save translated constraints" and "Save SMTLIB input" buttons

### Removed: Translated Constraints Display

- The algebraic translation of constraints is no longer shown to users
- Internal translation for PopperSAT will use multi-layer LPS encoding (too complex to display)
- "Save translated constraints" and "Save SMTLIB input" buttons removed
- "Save table as image" button retained for SAT results

### Added: LPS Solver Infrastructure

New file `src/lps_solver.ts` with core LPS (Lexicographic Probability System) solver infrastructure:

- **Layer assignments**: Maps conditioning events to layers (0 = abnormal, 1+ = normal at that layer)
- **Consistency checking**: Validates assignments (⊥ must be abnormal, ⊤ normal at layer 1, subset constraints)
- **SMTLIB generation**: Division-free encoding where `n = p · d` instead of `p = n/d`
- **Constraint transformation**: Converts user constraints to QF_NRA with fresh variables for probabilities

**Key functions:**
- `extractConditioningEvents()`: Finds all P(φ|ψ) conditioning events in constraints
- `generateLayerAssignments()`: Enumerates possible layer assignments
- `generateSMTLIBForAssignment()`: Creates complete SMTLIB input for a layer assignment
- `transformConstraintToSMTLIB()`: Division-free encoding of constraints

### Improved: Popper Model Display Uses Real State Values

- The conditional probability table now uses actual state assignments from the solver
- Previously used a uniform distribution stub; now uses μ(φ∩ψ)/μ(ψ) from solved state values
- Properly handles abnormal propositions (returns 1 when conditioning on zero-probability events)

### Completed: LPS Solver UI Integration

- Replaced `pr_sat_wrapped` with `solveLPS` in the main search workflow
- UI now uses the LPS solver for all constraint solving
- Added `PopperSATResult` type that includes both the standard result format and LPS-specific data
- `lpsModelToPopperModel()` converts LPS solver output to the `PopperModel` interface for display

**Changes:**
- `src/text_to_display.ts`:
  - `start_search_solver` now calls `solveLPS()` instead of `pr_sat_wrapped()`
  - Added `PopperSATResult` type extending `PrSATResult` with `popperModel` and `lpsResult`
  - Removed unused `pr_sat_wrapped` import and `cancel_fallback` function

### Completed: Model Evaluator Integration

- Model evaluator now uses the Popper model for evaluating expressions
- Added `evaluateWithPopperModel()` function to evaluate constraints and real expressions using Popper semantics
- Added `sentenceToProposition()` to convert sentences to propositions for evaluation
- Handles free variable checking and division-by-zero errors appropriately

**Changes:**
- `src/popper.ts`:
  - Added `sentenceToProposition()`: Converts a Sentence to a Proposition (set of state indices)
  - Added `evaluateRealExpr()`: Evaluates real expressions using Popper model's conditional probability
  - Added `evaluateConstraint()`: Evaluates boolean constraints using Popper model
  - Added `evaluateWithPopperModel()`: Main entry point for evaluation
- `src/text_to_display.ts`:
  - Updated `evaluate` function in SAT result to use `evaluateWithPopperModel()`
  - Checks for undeclared variables before evaluation
  - Returns proper `FancyEvaluatorOutput` types for display

### Completed: Multi-Layer Abnormality Handling

- LPS solver now extracts actual layer variable values from Z3 model
- Added `model_to_named_assignments()` to extract all variable values by name
- Updated `WrappedSolverResult` to include `named_assignments` field
- Abnormality is now properly computed: a proposition is abnormal only if it has zero mass at ALL layers
- `lpsModelToPopperModel()` computes abnormality by checking all layers

**Changes:**
- `src/z3_integration.ts`:
  - Updated `model_to_assigned_exprs()` to skip non-matching variable names (handles both PrSAT and LPS formats)
  - Added `model_to_named_assignments()`: Extracts all variable values keyed by name
  - Updated `WrappedSolverResult` type to include `named_assignments: Record<string, number>`
- `src/lps_solver.ts`:
  - Updated `solveLPS()` to extract actual layer values using `named_assignments`
  - Properly parses `a_k_s` format (layer k, state s)

### Added: Popper-Specific Test Suite

New test file `src/popper.spec.ts` with 19 tests covering:
- `sentenceToProposition()` utility function
- Proposition operations (entails, mutuallyExclusive, conjoin)
- LPS solver (SAT, UNSAT, conditional probability, Bayes theorem)
- Popper model evaluation (P(⊤|⊤)=1, P(A|A)=1, P(φ|⊥)=1, additivity)
- `evaluateWithPopperModel()` for constraints and expressions

**Bug fixes:**
- Fixed infinite recursion in `extractConditioningEvents()` - was incorrectly processing Sentence as RealExpr

**Current State**:
- LPS solver fully integrated with actual Z3 model values
- Multi-layer abnormality properly computed
- Model evaluator uses Popper model for evaluation
- Division-free SMTLIB encoding working
- All tests passing (564 passed, 23 skipped)

## 2026-01-28

### Fixed: False "Division by zero!" in Model Evaluator

- Division-by-zero check now correctly handles the eliminated state variable
- Previously, `Pr(X | ~Y)` would incorrectly show "Division by zero!" even when `Pr(~Y) > 0`, because the eliminated state variable (e.g., `a_4`) was not substituted before evaluation — Z3's model completion assigned it 0

**Example:** With a model where `a_2 = 0` and `a_4 = 1/2`, evaluating `Pr(X | ~Y)` no longer falsely reports division by zero (`Pr(~Y) = a_2 + a_4 = 1/2`)

**Changes:**
- `src/z3_integration.ts`: Div-by-zero constraints now go through `eliminate_state_variable_index_in_constraint_or_real_expr()` before evaluation, matching what was already done for the main expression

### Fixed: Conditional Probability Division by Zero

- Model evaluator now correctly shows "Division by zero!" for conditional probabilities when the condition has probability zero
- Previously, `Pr(A | B)` would incorrectly evaluate to `0` when `Pr(B) = 0`; now it correctly reports undefined (0/0)

**Example:** With a model where `Pr(~Q) = 0`, evaluating `Pr(P | ~Q)` now shows "Division by zero!" instead of `0`

**Changes:**
- `src/pr_sat.ts`: `div0_conditions_in_real_expr()` now generates a div-by-zero check for `given_probability` expressions
- `src/z3_integration.ts`:
  - Fixed `real_expr_to_arith()` to construct state variable sums symbolically (was incorrectly evaluating the first variable)
  - Added `model_completion` parameter to `model.eval()` to correctly evaluate eliminated state variables in div-by-zero checks

### Updated: Video Demo Link

- Changed video demo URL to `https://youtu.be/F_WbzKr7qJQ`

**Changes:**
- `src/text_to_display.ts`: Updated link in the intro section

## 2026-01-26

### Added: Save Table as Image Button

- New "Save table as image" button exports the probability table as a high-resolution PNG (2x pixel ratio)
- Button appears on its own row below the "Save translated constraints" and "Save SMTLIB input" buttons
- Only appears when a model is found (SAT result)
- The other two save buttons now appear for all solver results (SAT, UNSAT, cancelled, etc.)

**Changes:**
- `package.json`: Added `html-to-image` dependency
- `src/text_to_display.ts`: Added import and button logic in `start_search_solver`

### Simplified: Timeout Input

- Replaced hours/minutes/seconds fields with a single "seconds" field
- Default: 60 seconds, range: 1-3600 seconds

**Changes:**
- `src/text_to_display.ts`: Simplified `timeout()` function to single seconds input
- `tests/test_ids.ts`: Removed unused `hours` and `minutes` test IDs
- `tests/simple.spec.ts`: Updated `set_timeout()` helper function

## 2026-01-25

### Updated: Video Demo Link

- Changed video demo URL to `https://youtu.be/KKVGHH0zCQM`
- Link text changed from "brief video demo" to "Here"

**Changes:**
- `src/text_to_display.ts`: Updated link in the intro section

### Added: Demo Text File Download Link

- Added link to download the demo text file after the video demo sentence
- Link points to `https://fitelson.org/PrSAT/PrSAT_3.0_demo_examples.txt`

**Changes:**
- `src/text_to_display.ts`: Added download link in the intro section

### Changed: Consistent State Variable Naming

- State variables now use `a_i` naming (1-indexed) throughout the application
- Previously, saved constraints and SMTLIB output used `s_i` (0-indexed) while the HTML display used `a_i` (1-indexed)
- Now all outputs are consistent: `a_1`, `a_2`, etc.

**Changes:**
- `src/pr_sat.ts`: `state_index_id()` now returns `a_${index + 1}` instead of `s_${index}`
- `src/z3_integration.ts`: `model_to_assigned_exprs()` now converts 1-indexed variable names back to 0-indexed internal indices when parsing Z3 model output

### Improved: Immediate Display of Translated Constraints

- Translated constraints now appear immediately when "Find Model" is pressed, before the solver starts searching
- Previously, constraints only appeared after the solver finished
- Save buttons ("Save translated constraints", "Save SMTLIB input") appear once solving completes

**Changes:**
- `src/z3_integration.ts`: Added `onTranslated` callback to `SolverOptions2`
- `src/text_to_display.ts`: Updated `start_search_solver` to display constraints via the callback

### Fixed: Cancel/Timeout Now Preserves Display

- Translated constraints and probability table now remain visible after cancel or timeout
- Previously, cancelling a search would clear the bottom part of the page

**Root Cause:** When Z3 reinitializes during cancel, it triggered `invalidate()` while state was still 'looking', which set state to 'waiting' and cleared the display.

**Changes:**
- `src/z3_integration.ts`: Z3 now reinitializes after any cancel, ensuring clean state for next search
- `src/text_to_display.ts`:
  - `invalidate()` now skips when state is 'looking' to prevent clearing display during cancel
  - Removed page reload from `cancel_fallback` - Z3 reinitialization is sufficient
  - Exception state now re-enables the "Find Model" button

### Added: Clear Button for Evaluate Model

- Added "Clear" button next to "Evaluate model" heading
- Clicking it resets the section to its initial state (one empty input box)

**Changes:**
- `src/text_to_display.ts`: Added `clear_all()` function and Clear button in `model_evaluators()`

## 2026-01-24

### Updated: Video Demo Link

- Changed video demo link to `https://www.youtube.com/watch?v=HkccWiMYI5Q`

## 2026-01-23

### Updated: Z3 Solver

- Upgraded `z3-solver` npm package from 4.14.0 to 4.15.4
- Updated WASM files in `public/` and `dist/` directories

## 2026-01-22

### Fixed: iOS Safari Compatibility

**Problem:** The app was showing "Unexpected Exception! [object Event]" on iOS Safari, while working fine on desktop browsers.

**Root Cause:** Two issues were identified:
1. CSS `@import` for Google Fonts conflicted with cross-origin isolation headers required by Z3's SharedArrayBuffer
2. The server (ICDSoft/Apache) needed specific headers to enable SharedArrayBuffer on mobile Safari

**Changes:**

#### `src/style.css`
- Removed `@import url('https://fonts.googleapis.com/...')` statement
- Google Fonts CSS imports break cross-origin isolation (COEP) on iOS Safari

#### `index.html`
- Changed page title from "Vite + TS" to "PrSAT 3.0"
- Added Google Fonts via `<link>` tags with `crossorigin` attribute (compatible with COEP)

#### `src/text_to_display.ts`
- Improved `window.onerror` handler to provide meaningful error messages
- Added specific detection for Z3 WebAssembly loading failures
- Error messages now include source location (file:line:column)

#### `dist/.htaccess` (new file)
- Added Apache configuration for proper WASM support and cross-origin isolation
- **Important:** This file must be uploaded to the server with the dist folder

### Notes

- The `.htaccess` file is required for iOS Safari compatibility on Apache servers (e.g., ICDSoft)
- GitHub Pages (imapersonman.github.io) handles these headers automatically
- Desktop browsers are more lenient with cross-origin isolation requirements

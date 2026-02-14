# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

PopperSAT is a decision procedure for checking satisfiability of constraints on **Popper probability functions**. Unlike Kolmogorov probability where P(A) is primitive, Popper functions have P(A|B) as the primitive—allowing conditioning on zero-probability events.

**Key semantic rule**: If ψ is "abnormal" (zero probability at all layers), then P(φ|ψ) = 1 for ALL φ.

**Important**: This is a local deployment build manually uploaded to fitelson.org. Do not use git push; changes are manually deployed by copying the `dist/` folder.

## Commands

```bash
npm run dev          # Start dev server at http://localhost:5173/
npm run build        # Compile TypeScript + bundle with Vite → dist/
npm run test         # Run Vitest + Playwright tests
npm run test-single  # Run Vitest with --allowOnly (for focused tests)
npm run copy-files   # Copy Z3 WASM files to public/ (required before build)
```

## Architecture

### Core Algorithm: Lexicographic Probability Systems (LPS)

The solver uses multiple layers of probability measures (μ₁, ..., μ_K). For P(φ|ψ):
1. Find first layer k where μ_k(ψ) > 0
2. Return P(φ|ψ) = μ_k(φ∧ψ) / μ_k(ψ)
3. If no such layer exists, ψ is "abnormal" → return 1

Division-free Z3 encoding: Instead of `p = n/d`, uses `n = p · d` to avoid division constraints.

### Type System

Three core AST types in `src/types.ts` using discriminated unions:
- **Sentence**: Propositional logic (atoms, ~, &, ∨, →, ↔)
- **RealExpr**: Real-valued expressions including `Pr(φ | ψ)` — no bare `Pr(A)` allowed
- **Constraint**: Boolean formulas with comparisons (=, ≠, <, ≤, >, ≥)

Key data types in `src/z3_integration.ts`:
- `Rational = {numer: bigint, denom: bigint}` — exact rational arithmetic
- `QuadraticSurd = {a, b: Rational, c: bigint}` — represents a + b√c
- `ExactNumber` — tagged union of rational, surd, or float

### Key Source Files

| File | Purpose |
|------|---------|
| `lps_solver.ts` | Main solving algorithm: layer assignments, SMTLIB generation |
| `popper.ts` | Popper utilities: propositions, axiom verification, model evaluation |
| `z3_integration.ts` | Z3 interface, exact arithmetic types, model extraction |
| `text_to_display.ts` | Main UI component, user interaction |
| `pr_sat.ts` | Truth table, AST builders, SMTLIB translation |
| `types.ts` | Core AST type definitions |
| `parser.ts` | User input parsing using Parsimmon |

### Important Types

```typescript
type Proposition = Set<number>  // Set of state indices where proposition is true
type PopperModel = {
  isAbnormal: (prop: Proposition) => boolean
  conditionalProbability: (phi: Proposition, psi: Proposition) => number | undefined
}
type LayerAssignment = Map<string, number>  // proposition key → layer (0 = abnormal)
```

## Technical Notes

- Z3 WebAssembly requires SharedArrayBuffer, which needs COEP/COOP headers (configured in vite.config.ts)
- Truth table generates 2^n states for n atomic sentences
- Conditional probability table shows 2^(2^n) × 2^(2^n) entries
- UI conditionally shows table/axiom verification based on problem size (n ≤ 2: both, n = 3: table only, n ≥ 4: neither)

/**
 * PopperSAT utilities for conditional probability tables
 *
 * A Popper function is a two-place probability function P(φ | ψ) where:
 * - For normal ψ (positive probability at some layer): standard conditional probability
 * - For abnormal ψ (zero probability at all layers): P(φ | ψ) = 1 for all φ
 */

import { TruthTable, sentence_builder } from "./pr_sat"
import { PrSat, SentenceMap } from "./types"
import {
  ExactNumber, exactAdd, exactSub, exactMul, exactDiv, exactNeg, exactPow,
  exactFromRational, rationalFromInt, exactIsZero, EXACT_ONE
} from "./z3_integration"

type Sentence = PrSat['Sentence']

const { val, or } = sentence_builder

/**
 * A proposition represented as a set of state indices where it's true.
 * For n atomic sentences, states are numbered 0 to 2^n - 1.
 * The empty set represents ⊥ (contradiction).
 * The full set {0, 1, ..., 2^n - 1} represents ⊤ (tautology).
 */
export type Proposition = Set<number>

/**
 * Generate all 2^(2^n) propositions for a truth table with n atomic sentences.
 * Each proposition is represented as a Set of state indices.
 *
 * Returns propositions ordered by their "proposition index" (0 to 2^(2^n) - 1),
 * where the proposition index is a bitmask indicating which states are included.
 */
export function generateAllPropositions(tt: TruthTable): Proposition[] {
  const nStates = tt.n_states()
  const nPropositions = Math.pow(2, nStates)
  const propositions: Proposition[] = []

  for (let propIndex = 0; propIndex < nPropositions; propIndex++) {
    const prop = new Set<number>()
    for (let stateIndex = 0; stateIndex < nStates; stateIndex++) {
      // If bit stateIndex is set in propIndex, include that state
      if ((propIndex & (1 << stateIndex)) !== 0) {
        prop.add(stateIndex)
      }
    }
    propositions.push(prop)
  }

  return propositions
}

/**
 * Convert a proposition (set of state indices) to a Sentence AST.
 * Returns a disjunction of the states (minterms) where the proposition is true.
 */
export function propositionToSentence(tt: TruthTable, prop: Proposition): Sentence {
  if (prop.size === 0) {
    return val(false) // ⊥
  }

  if (prop.size === tt.n_states()) {
    return val(true) // ⊤
  }

  const stateIndices = Array.from(prop).sort((a, b) => a - b)
  let result: Sentence | undefined = undefined

  for (const stateIndex of stateIndices) {
    const stateSentence = tt.state_from_index(stateIndex)
    if (result === undefined) {
      result = stateSentence
    } else {
      result = or(result, stateSentence)
    }
  }

  return result!
}

/**
 * Convert a Sentence to a Proposition (set of state indices where sentence is true).
 * This is the inverse of propositionToSentence.
 */
export function sentenceToProposition(tt: TruthTable, sentence: Sentence): Proposition {
  const dnf = tt.compute_dnf(sentence)
  return new Set(dnf)
}

/**
 * Generate a short label for a proposition: p₁, p₂, etc.
 * Index is 1-based for readability.
 */
export function propositionLabel(_tt: TruthTable, _prop: Proposition, index: number): string {
  // Use subscript digits for cleaner display
  const subscriptDigits = '₀₁₂₃₄₅₆₇₈₉'
  const indexStr = (index + 1).toString()
  const subscript = indexStr.split('').map(d => subscriptDigits[parseInt(d)]).join('')
  return `p${subscript}`
}

/**
 * Generate the DNF representation of a proposition for the legend.
 */
export function propositionDNF(tt: TruthTable, prop: Proposition): string {
  const nStates = tt.n_states()

  // Special cases
  if (prop.size === 0) {
    return '⊥'
  }
  if (prop.size === nStates) {
    return '⊤'
  }

  const letters = Array.from(tt.letters())

  // Check if it's a single literal (half the states)
  if (prop.size === nStates / 2 && letters.length > 0) {
    const literalLabel = tryMatchLiteral(tt, prop, letters)
    if (literalLabel) {
      return literalLabel
    }
  }

  // Check if complement is simpler (for propositions covering most states)
  const complement = new Set<number>()
  for (let i = 0; i < nStates; i++) {
    if (!prop.has(i)) {
      complement.add(i)
    }
  }

  // If complement is smaller, express as negation of DNF
  if (complement.size > 0 && complement.size < prop.size && complement.size <= 3) {
    const compLabels = Array.from(complement).sort((a, b) => a - b).map(i => stateLabel(letters, i))
    return `~(${compLabels.join(' ∨ ')})`
  }

  // Show as disjunction of states (DNF)
  const stateLabels = Array.from(prop).sort((a, b) => a - b).map(i => stateLabel(letters, i))
  return stateLabels.join(' ∨ ')
}

/**
 * Generate a label for a single state (minterm).
 */
function stateLabel(letters: SentenceMap['letter'][], stateIndex: number): string {
  if (letters.length === 0) {
    return '⊤'
  }

  const parts: string[] = []
  const binStr = stateIndex.toString(2).padStart(letters.length, '0')

  for (let i = 0; i < letters.length; i++) {
    const letter = letters[i]
    const letterStr = letter.id + (letter.index > 0 ? letter.index.toString() : '')
    const bit = binStr[i]
    if (bit === '0') {
      parts.push(letterStr)
    } else {
      parts.push(`~${letterStr}`)
    }
  }

  return parts.join('&')
}

/**
 * Try to match a proposition to a single literal (A, B, ¬A, ¬B, etc.)
 */
function tryMatchLiteral(tt: TruthTable, prop: Proposition, letters: SentenceMap['letter'][]): string | null {
  for (const letter of letters) {
    // Check if prop matches this letter being true
    const letterTrue = new Set<number>()
    const letterFalse = new Set<number>()

    for (let i = 0; i < tt.n_states(); i++) {
      if (tt.letter_value_from_index(letter, i)) {
        letterTrue.add(i)
      } else {
        letterFalse.add(i)
      }
    }

    const letterStr = letter.id + (letter.index > 0 ? letter.index.toString() : '')

    if (setsEqual(prop, letterTrue)) {
      return letterStr
    }
    if (setsEqual(prop, letterFalse)) {
      return `~${letterStr}`
    }
  }

  return null
}

function setsEqual<T>(a: Set<T>, b: Set<T>): boolean {
  if (a.size !== b.size) return false
  for (const x of a) {
    if (!b.has(x)) return false
  }
  return true
}

/**
 * Check if proposition p entails proposition q (p ⊆ q as sets of states).
 */
export function entails(p: Proposition, q: Proposition): boolean {
  for (const state of p) {
    if (!q.has(state)) {
      return false
    }
  }
  return true
}

/**
 * Check if propositions p and q are mutually exclusive (p ∩ q = ∅).
 */
export function mutuallyExclusive(p: Proposition, q: Proposition): boolean {
  for (const state of p) {
    if (q.has(state)) {
      return false
    }
  }
  return true
}

/**
 * Compute the conjunction of two propositions (set intersection).
 */
export function conjoin(p: Proposition, q: Proposition): Proposition {
  const result = new Set<number>()
  for (const state of p) {
    if (q.has(state)) {
      result.add(state)
    }
  }
  return result
}

/**
 * Placeholder type for a Popper model.
 * This will be replaced with the actual LPS model structure.
 */
export type PopperModel = {
  /**
   * Check if a proposition is abnormal (zero probability at all layers).
   * For now, only ⊥ is abnormal.
   */
  isAbnormal: (prop: Proposition) => boolean

  /**
   * Compute P(φ | ψ) for normal ψ.
   * Returns undefined if ψ is abnormal (caller should return 1).
   */
  conditionalProbability: (phi: Proposition, psi: Proposition) => number | undefined

  /**
   * Compute P(φ | ψ) as exact number (rational if possible, float for irrationals).
   * Returns undefined if not available (e.g., stub models).
   */
  conditionalProbabilityExact?: (phi: Proposition, psi: Proposition) => ExactNumber | undefined
}

/**
 * Create a stub Popper model for testing the display.
 * This always treats ⊥ as abnormal, and uses placeholder values.
 */
export function createStubPopperModel(_tt: TruthTable): PopperModel {
  return {
    isAbnormal: (prop: Proposition) => prop.size === 0,

    conditionalProbability: (phi: Proposition, psi: Proposition) => {
      // If conditioning event is abnormal, return undefined (caller handles as 1)
      if (psi.size === 0) {
        return undefined
      }

      // If phi and psi are mutually exclusive, return 0
      if (mutuallyExclusive(phi, psi)) {
        return 0
      }

      // If psi entails phi, return 1
      if (entails(psi, phi)) {
        return 1
      }

      // Otherwise, compute as |phi ∩ psi| / |psi| (uniform distribution placeholder)
      const intersection = conjoin(phi, psi)
      return intersection.size / psi.size
    }
  }
}

/**
 * Compute the full conditional probability table for a Popper model.
 * Returns a 2D array where table[i][j] = P(proposition_j | proposition_i).
 * Rows are conditioning events (ψ), columns are propositions (φ).
 */
export function computeConditionalProbabilityTable(
  _tt: TruthTable,
  model: PopperModel,
  propositions: Proposition[]
): number[][] {
  const table: number[][] = []

  for (const psi of propositions) {
    const row: number[] = []

    if (model.isAbnormal(psi)) {
      // Abnormal conditioning: P(φ | ψ) = 1 for all φ
      for (const _phi of propositions) {
        row.push(1)
      }
    } else {
      for (const phi of propositions) {
        const prob = model.conditionalProbability(phi, psi)
        row.push(prob ?? 1) // Should not happen for normal psi, but fallback to 1
      }
    }

    table.push(row)
  }

  return table
}

// Types for evaluation
type RealExpr = PrSat['RealExpr']
type Constraint = PrSat['Constraint']
type ConstraintOrRealExpr =
  | { tag: 'constraint', constraint: Constraint }
  | { tag: 'real_expr', real_expr: RealExpr }

/**
 * Evaluate a RealExpr using a Popper model.
 * Returns the numerical value of the expression.
 */
export function evaluateRealExpr(
  tt: TruthTable,
  model: PopperModel,
  expr: RealExpr
): number {
  const evaluate = (e: RealExpr): number => evaluateRealExpr(tt, model, e)

  switch (expr.tag) {
    case 'literal':
      return expr.value
    case 'variable':
      throw new Error(`Cannot evaluate free variable '${expr.id}'`)
    case 'state_variable_sum':
      throw new Error('state_variable_sum should not appear in user expressions')
    case 'given_probability': {
      const phi = sentenceToProposition(tt, expr.arg)
      const psi = sentenceToProposition(tt, expr.given)

      // If conditioning on abnormal, return 1
      if (model.isAbnormal(psi)) {
        return 1
      }

      const prob = model.conditionalProbability(phi, psi)
      return prob ?? 1  // Fallback to 1 for abnormal (shouldn't happen after check)
    }
    case 'negative':
      return -evaluate(expr.expr)
    case 'plus':
      return evaluate(expr.left) + evaluate(expr.right)
    case 'minus':
      return evaluate(expr.left) - evaluate(expr.right)
    case 'multiply':
      return evaluate(expr.left) * evaluate(expr.right)
    case 'divide': {
      const denom = evaluate(expr.denominator)
      if (denom === 0) {
        throw new Error('Division by zero')
      }
      return evaluate(expr.numerator) / denom
    }
    case 'power':
      return Math.pow(evaluate(expr.base), evaluate(expr.exponent))
    default:
      throw new Error(`Unknown RealExpr tag: ${(expr as RealExpr).tag}`)
  }
}

/**
 * Evaluate a Constraint using a Popper model.
 * Returns true or false.
 */
export function evaluateConstraint(
  tt: TruthTable,
  model: PopperModel,
  constraint: Constraint
): boolean {
  const evalReal = (e: RealExpr): number => evaluateRealExpr(tt, model, e)
  const evalCons = (c: Constraint): boolean => evaluateConstraint(tt, model, c)

  switch (constraint.tag) {
    case 'equal':
      return evalReal(constraint.left) === evalReal(constraint.right)
    case 'not_equal':
      return evalReal(constraint.left) !== evalReal(constraint.right)
    case 'less_than':
      return evalReal(constraint.left) < evalReal(constraint.right)
    case 'less_than_or_equal':
      return evalReal(constraint.left) <= evalReal(constraint.right)
    case 'greater_than':
      return evalReal(constraint.left) > evalReal(constraint.right)
    case 'greater_than_or_equal':
      return evalReal(constraint.left) >= evalReal(constraint.right)
    case 'negation':
      return !evalCons(constraint.constraint)
    case 'conjunction':
      return evalCons(constraint.left) && evalCons(constraint.right)
    case 'disjunction':
      return evalCons(constraint.left) || evalCons(constraint.right)
    case 'conditional':
      return !evalCons(constraint.left) || evalCons(constraint.right)
    case 'biconditional':
      return evalCons(constraint.left) === evalCons(constraint.right)
    default:
      throw new Error(`Unknown Constraint tag: ${(constraint as Constraint).tag}`)
  }
}

/**
 * Evaluate a ConstraintOrRealExpr using a Popper model.
 * Returns either a boolean (for constraints) or a number (for real expressions).
 */
export function evaluateWithPopperModel(
  tt: TruthTable,
  model: PopperModel,
  expr: ConstraintOrRealExpr
): boolean | number {
  if (expr.tag === 'constraint') {
    return evaluateConstraint(tt, model, expr.constraint)
  } else {
    return evaluateRealExpr(tt, model, expr.real_expr)
  }
}

/**
 * Evaluate a RealExpr using a Popper model, returning an ExactNumber.
 * Preserves exact rational arithmetic when possible.
 */
export function evaluateRealExprExact(
  tt: TruthTable,
  model: PopperModel,
  expr: RealExpr
): ExactNumber {
  const evaluate = (e: RealExpr): ExactNumber => evaluateRealExprExact(tt, model, e)

  switch (expr.tag) {
    case 'literal':
      // Convert literal to exact rational if it's a simple fraction
      const val = expr.value
      if (Number.isInteger(val)) {
        return exactFromRational(rationalFromInt(BigInt(val)))
      }
      // Try to convert decimal to rational
      const str = val.toString()
      const decimalIndex = str.indexOf('.')
      if (decimalIndex !== -1) {
        const decimals = str.length - decimalIndex - 1
        const denom = BigInt(10 ** decimals)
        const numer = BigInt(Math.round(val * Number(denom)))
        return exactFromRational({ numer, denom })
      }
      return { tag: 'float', value: val }

    case 'variable':
      throw new Error(`Cannot evaluate free variable '${expr.id}'`)

    case 'state_variable_sum':
      throw new Error('state_variable_sum should not appear in user expressions')

    case 'given_probability': {
      const phi = sentenceToProposition(tt, expr.arg)
      const psi = sentenceToProposition(tt, expr.given)

      // If conditioning on abnormal, return 1
      if (model.isAbnormal(psi)) {
        return EXACT_ONE
      }

      // Use exact probability if available
      if (model.conditionalProbabilityExact) {
        const prob = model.conditionalProbabilityExact(phi, psi)
        if (prob) return prob
      }

      // Fallback to float
      const prob = model.conditionalProbability(phi, psi)
      return { tag: 'float', value: prob ?? 1 }
    }

    case 'negative':
      return exactNeg(evaluate(expr.expr))

    case 'plus':
      return exactAdd(evaluate(expr.left), evaluate(expr.right))

    case 'minus':
      return exactSub(evaluate(expr.left), evaluate(expr.right))

    case 'multiply':
      return exactMul(evaluate(expr.left), evaluate(expr.right))

    case 'divide': {
      const denom = evaluate(expr.denominator)
      if (exactIsZero(denom)) {
        throw new Error('Division by zero')
      }
      return exactDiv(evaluate(expr.numerator), denom)
    }

    case 'power':
      return exactPow(evaluate(expr.base), evaluate(expr.exponent))

    default:
      throw new Error(`Unknown RealExpr tag: ${(expr as RealExpr).tag}`)
  }
}

/**
 * Evaluate a ConstraintOrRealExpr using a Popper model, returning exact values.
 * Returns either a boolean (for constraints) or an ExactNumber (for real expressions).
 */
export function evaluateWithPopperModelExact(
  tt: TruthTable,
  model: PopperModel,
  expr: ConstraintOrRealExpr
): boolean | ExactNumber {
  if (expr.tag === 'constraint') {
    return evaluateConstraint(tt, model, expr.constraint)
  } else {
    return evaluateRealExprExact(tt, model, expr.real_expr)
  }
}

/**
 * Compute the complement of a proposition (all states not in prop).
 */
export function complement(nStates: number, prop: Proposition): Proposition {
  const result = new Set<number>()
  for (let i = 0; i < nStates; i++) {
    if (!prop.has(i)) {
      result.add(i)
    }
  }
  return result
}

/**
 * Format a probability value for display (helper for axiom verification messages).
 */
function formatProb(p: number): string {
  if (Number.isInteger(p)) return p.toString()
  return p.toFixed(4).replace(/\.?0+$/, '')
}

/**
 * Result of checking a single axiom.
 */
export type AxiomCheckResult = {
  axiom: number
  name: string
  satisfied: boolean
  message: string
}

/**
 * Verify that a Popper model satisfies Popper's axioms.
 *
 * The axioms (from Popper 1955, simplified):
 * 0. Non-triviality: Some P[E|F] ≠ P[G|H]
 * 1. Reflexivity: P[A | A] ≥ P[B | B] for all A, B
 * 2. Commutativity: P[A | (B · C)] ≥ P[A | (C · B)] for all A, B, C
 * 3. Monotonicity: P[A | C] ≥ P[(A · B) | C] for all A, B, C
 * 4. Additivity/Abnormality: P[A | B] + P[~A | B] = P[B | B] OR P[D | B] = P[B | B] for all D
 * 5. Multiplication: P[(A · B) | C] = P[A | (B · C)] × P[B | C] for all A, B, C
 */
export function verifyPopperAxioms(
  tt: TruthTable,
  model: PopperModel,
  propositions: Proposition[]
): AxiomCheckResult[] {
  const results: AxiomCheckResult[] = []
  const nStates = tt.n_states()

  // Helper to get probability, handling abnormal case
  const P = (phi: Proposition, psi: Proposition): number => {
    if (model.isAbnormal(psi)) return 1
    return model.conditionalProbability(phi, psi) ?? 1
  }

  // Helper for proposition DNF (shortened version for messages)
  const propDNF = (prop: Proposition): string => {
    if (prop.size === 0) return '⊥'
    if (prop.size === nStates) return '⊤'
    const arr = Array.from(prop).sort((a, b) => a - b)
    if (arr.length <= 3) return `{${arr.join(',')}}`
    return `{${arr.slice(0, 2).join(',')},...}`
  }

  // Axiom 0: Non-triviality
  let foundDifferent = false
  outer: for (const e of propositions) {
    for (const f of propositions) {
      for (const g of propositions) {
        for (const h of propositions) {
          if (P(e, f) !== P(g, h)) {
            foundDifferent = true
            break outer
          }
        }
      }
    }
  }
  results.push({
    axiom: 0,
    name: 'Non-triviality',
    satisfied: foundDifferent,
    message: foundDifferent
      ? 'Some P[E|F] ≠ P[G|H]'
      : 'All probabilities are equal (trivial model)'
  })

  // Axiom 1: Reflexivity - P[A | A] ≥ P[B | B] for all A, B
  // Since P[A|A] = 1 for normal A and 1 for abnormal A, this should always hold
  let axiom1Satisfied = true
  for (const a of propositions) {
    for (const b of propositions) {
      if (P(a, a) < P(b, b)) {
        axiom1Satisfied = false
        break
      }
    }
    if (!axiom1Satisfied) break
  }
  results.push({
    axiom: 1,
    name: 'Reflexivity',
    satisfied: axiom1Satisfied,
    message: axiom1Satisfied
      ? 'P[A | A] ≥ P[B | B] for all A, B'
      : 'Found A, B where P[A | A] < P[B | B]'
  })

  // Axiom 2: Commutativity - P[A | (B · C)] ≥ P[A | (C · B)]
  // Since (B · C) = (C · B), this is trivially satisfied
  results.push({
    axiom: 2,
    name: 'Conjunction commutativity',
    satisfied: true,
    message: 'P[A | (B · C)] = P[A | (C · B)] (conjunction is commutative)'
  })

  // Axiom 3: Monotonicity - P[A | C] ≥ P[(A · B) | C]
  let axiom3Satisfied = true
  let axiom3Counter: { a: Proposition, b: Proposition, c: Proposition, pAC: number, pABC: number } | null = null
  for (const a of propositions) {
    for (const b of propositions) {
      for (const c of propositions) {
        const ab = conjoin(a, b)
        const pAC = P(a, c)
        const pABC = P(ab, c)
        if (pAC < pABC - 1e-10) {  // Small tolerance for floating point
          axiom3Satisfied = false
          axiom3Counter = { a, b, c, pAC, pABC }
          break
        }
      }
      if (!axiom3Satisfied) break
    }
    if (!axiom3Satisfied) break
  }
  results.push({
    axiom: 3,
    name: 'Monotonicity',
    satisfied: axiom3Satisfied,
    message: axiom3Satisfied
      ? 'P[A | C] ≥ P[(A · B) | C] for all A, B, C'
      : `Counterexample: P[${propDNF(axiom3Counter!.a)} | ${propDNF(axiom3Counter!.c)}] = ${formatProb(axiom3Counter!.pAC)} < ${formatProb(axiom3Counter!.pABC)} = P[${propDNF(axiom3Counter!.a)}·${propDNF(axiom3Counter!.b)} | ${propDNF(axiom3Counter!.c)}]`
  })

  // Axiom 4: Additivity or Abnormality
  // For all B: either P[A | B] + P[~A | B] = P[B | B] for all A, OR P[D | B] = P[B | B] for all D
  let axiom4Satisfied = true
  let axiom4Counter: { b: Proposition, a: Proposition, pAB: number, pNotAB: number, pBB: number } | null = null

  for (const b of propositions) {
    const pBB = P(b, b)
    // Check if B is abnormal (all D have P[D|B] = P[B|B] = 1)
    let isAbnormal = true
    for (const d of propositions) {
      if (Math.abs(P(d, b) - pBB) > 1e-10) {
        isAbnormal = false
        break
      }
    }

    if (!isAbnormal) {
      // B is normal, so additivity must hold: P[A | B] + P[~A | B] = P[B | B]
      for (const a of propositions) {
        const notA = complement(nStates, a)
        const pAB = P(a, b)
        const pNotAB = P(notA, b)
        if (Math.abs(pAB + pNotAB - pBB) > 1e-10) {
          axiom4Satisfied = false
          axiom4Counter = { b, a, pAB, pNotAB, pBB }
          break
        }
      }
    }
    if (!axiom4Satisfied) break
  }

  results.push({
    axiom: 4,
    name: 'Additivity/Abnormality',
    satisfied: axiom4Satisfied,
    message: axiom4Satisfied
      ? 'For all B: additivity holds for normal B, abnormality condition holds for abnormal B'
      : `Counterexample: P[${propDNF(axiom4Counter!.a)} | ${propDNF(axiom4Counter!.b)}] + P[~${propDNF(axiom4Counter!.a)} | ${propDNF(axiom4Counter!.b)}] = ${formatProb(axiom4Counter!.pAB)} + ${formatProb(axiom4Counter!.pNotAB)} = ${formatProb(axiom4Counter!.pAB + axiom4Counter!.pNotAB)} ≠ ${formatProb(axiom4Counter!.pBB)} = P[${propDNF(axiom4Counter!.b)} | ${propDNF(axiom4Counter!.b)}]`
  })

  // Axiom 5: Multiplication (Chain Rule)
  // P[(A · B) | C] = P[A | (B · C)] × P[B | C]
  let axiom5Satisfied = true
  let axiom5Counter: { a: Proposition, b: Proposition, c: Proposition, lhs: number, rhs: number } | null = null

  for (const a of propositions) {
    for (const b of propositions) {
      for (const c of propositions) {
        const ab = conjoin(a, b)
        const bc = conjoin(b, c)
        const lhs = P(ab, c)
        const rhs = P(a, bc) * P(b, c)
        if (Math.abs(lhs - rhs) > 1e-10) {
          axiom5Satisfied = false
          axiom5Counter = { a, b, c, lhs, rhs }
          break
        }
      }
      if (!axiom5Satisfied) break
    }
    if (!axiom5Satisfied) break
  }

  results.push({
    axiom: 5,
    name: 'Multiplication',
    satisfied: axiom5Satisfied,
    message: axiom5Satisfied
      ? 'P[(A · B) | C] = P[A | (B · C)] × P[B | C] for all A, B, C'
      : `Counterexample: P[${propDNF(axiom5Counter!.a)}·${propDNF(axiom5Counter!.b)} | ${propDNF(axiom5Counter!.c)}] = ${formatProb(axiom5Counter!.lhs)} ≠ ${formatProb(axiom5Counter!.rhs)} = P[${propDNF(axiom5Counter!.a)} | ${propDNF(axiom5Counter!.b)}·${propDNF(axiom5Counter!.c)}] × P[${propDNF(axiom5Counter!.b)} | ${propDNF(axiom5Counter!.c)}]`
  })

  return results
}

/**
 * Tests for Popper-specific semantics and the LPS solver.
 *
 * Key Popper semantics:
 * - P(φ | ⊥) = 1 for all φ (conditioning on contradiction always gives 1)
 * - P(φ | ψ) = 1 when ψ is abnormal (zero mass at all layers)
 * - P(φ | ψ) follows standard conditional probability when ψ is normal
 */
import { describe, expect, test, beforeAll } from 'vitest'
import { constraint_builder, real_expr_builder, sentence_builder, TruthTable, variables_in_constraints } from './pr_sat'
import { init_z3, WrappedSolver } from './z3_integration'
import { solveLPS, lpsModelToPopperModel } from './lps_solver'
import {
  sentenceToProposition,
  evaluateRealExpr,
  evaluateConstraint,
  entails,
  mutuallyExclusive,
  conjoin
} from './popper'
import { PrSat } from './types'

type Sentence = PrSat['Sentence']
type RealExpr = PrSat['RealExpr']
type Constraint = PrSat['Constraint']

const { eq, gt, cnot } = constraint_builder
const { cpr, lit, multiply, plus } = real_expr_builder
const { and, not, letter, val } = sentence_builder

// Helper: unconditional probability in Popper's system is Pr(A | ⊤)
const pr = (s: Sentence): RealExpr => cpr(s, val(true))

const [A, B] = [letter('A'), letter('B')]

let solver: WrappedSolver

beforeAll(async () => {
  const z3_interface = await init_z3()
  const reinit = async () => {
    const z3 = await init_z3()
    return z3
  }
  solver = new WrappedSolver(z3_interface, reinit)
})

// Helper to create TruthTable from letter sentences
const makeTT = (letters: Sentence[]): TruthTable => {
  // Extract letter ids from sentences
  const letterIds = letters.map(l => {
    if (l.tag !== 'letter') throw new Error('Expected letter')
    return l as PrSat['Sentence'] & { tag: 'letter' }
  })
  return new TruthTable({ real: [], sentence: letterIds })
}

describe('Popper utilities', () => {
  describe('sentenceToProposition', () => {
    test('⊤ is all states', () => {
      const tt = makeTT([A])
      const prop = sentenceToProposition(tt, val(true))
      expect(prop.size).toBe(2)  // 2^1 = 2 states
      expect(prop.has(0)).toBe(true)
      expect(prop.has(1)).toBe(true)
    })

    test('⊥ is empty set', () => {
      const tt = makeTT([A])
      const prop = sentenceToProposition(tt, val(false))
      expect(prop.size).toBe(0)
    })

    test('A is half the states', () => {
      const tt = makeTT([A, B])
      const prop = sentenceToProposition(tt, A)
      expect(prop.size).toBe(2)  // 2 of 4 states
    })

    test('A ∧ B is one state (for 2 variables)', () => {
      const tt = makeTT([A, B])
      const prop = sentenceToProposition(tt, and(A, B))
      expect(prop.size).toBe(1)
    })
  })

  describe('proposition operations', () => {
    test('entails: A ∧ B entails A', () => {
      const tt = makeTT([A, B])
      const propAB = sentenceToProposition(tt, and(A, B))
      const propA = sentenceToProposition(tt, A)
      expect(entails(propAB, propA)).toBe(true)
    })

    test('entails: A does not entail A ∧ B', () => {
      const tt = makeTT([A, B])
      const propAB = sentenceToProposition(tt, and(A, B))
      const propA = sentenceToProposition(tt, A)
      expect(entails(propA, propAB)).toBe(false)
    })

    test('mutuallyExclusive: A and ¬A', () => {
      const tt = makeTT([A])
      const propA = sentenceToProposition(tt, A)
      const propNotA = sentenceToProposition(tt, not(A))
      expect(mutuallyExclusive(propA, propNotA)).toBe(true)
    })

    test('conjoin: A ∧ B', () => {
      const tt = makeTT([A, B])
      const propA = sentenceToProposition(tt, A)
      const propB = sentenceToProposition(tt, B)
      const propAB = conjoin(propA, propB)
      const expectedAB = sentenceToProposition(tt, and(A, B))
      expect(propAB).toEqual(expectedAB)
    })
  })
})

describe('LPS Solver', () => {
  test('simple SAT', async () => {
    const constraints: Constraint[] = [
      gt(pr(A), lit(0))  // Pr(A | ⊤) > 0
    ]
    const tt = new TruthTable(variables_in_constraints(constraints))
    const result = await solveLPS(solver, tt, constraints, 2)

    expect(result.status).toBe('sat')
  }, 30000)

  test('simple UNSAT', async () => {
    const constraints: Constraint[] = [
      gt(pr(A), lit(1))  // Pr(A | ⊤) > 1 is impossible
    ]
    const tt = new TruthTable(variables_in_constraints(constraints))
    const result = await solveLPS(solver, tt, constraints, 2)

    expect(result.status).toBe('unsat')
  }, 30000)

  test('conditional probability basic', async () => {
    const constraints: Constraint[] = [
      eq(cpr(A, B), lit(0.5))  // Pr(A | B) = 0.5
    ]
    const tt = new TruthTable(variables_in_constraints(constraints))
    const result = await solveLPS(solver, tt, constraints, 2)

    expect(result.status).toBe('sat')
  }, 30000)

  test('Bayes theorem holds', async () => {
    // Pr(A|B) * Pr(B) = Pr(B|A) * Pr(A)
    const constraints: Constraint[] = [
      cnot(eq(
        multiply(cpr(A, B), pr(B)),
        multiply(cpr(B, A), pr(A))
      ))
    ]
    const tt = new TruthTable(variables_in_constraints(constraints))
    const result = await solveLPS(solver, tt, constraints, 2)

    // Should be UNSAT because Bayes' theorem is a logical truth
    expect(result.status).toBe('unsat')
  }, 30000)
})

describe('Popper model evaluation', () => {
  test('P(⊤ | ⊤) = 1', async () => {
    const constraints: Constraint[] = [
      gt(pr(A), lit(0))  // Just need some constraint to get a model
    ]
    const tt = new TruthTable(variables_in_constraints(constraints))
    const result = await solveLPS(solver, tt, constraints, 2)

    expect(result.status).toBe('sat')
    if (result.status !== 'sat') return

    const model = lpsModelToPopperModel(tt, result.model)

    // P(⊤ | ⊤) = 1
    const top = sentenceToProposition(tt, val(true))
    expect(model.conditionalProbability(top, top)).toBe(1)
  }, 30000)

  test('P(A | A) = 1 (A normal)', async () => {
    const constraints: Constraint[] = [
      gt(pr(A), lit(0))  // Make A normal
    ]
    const tt = new TruthTable(variables_in_constraints(constraints))
    const result = await solveLPS(solver, tt, constraints, 2)

    expect(result.status).toBe('sat')
    if (result.status !== 'sat') return

    const model = lpsModelToPopperModel(tt, result.model)
    const propA = sentenceToProposition(tt, A)

    // P(A | A) = 1
    expect(model.conditionalProbability(propA, propA)).toBe(1)
  }, 30000)

  test('P(φ | ⊥) = 1 (abnormal conditioning)', async () => {
    const constraints: Constraint[] = [
      gt(pr(A), lit(0))
    ]
    const tt = new TruthTable(variables_in_constraints(constraints))
    const result = await solveLPS(solver, tt, constraints, 2)

    expect(result.status).toBe('sat')
    if (result.status !== 'sat') return

    const model = lpsModelToPopperModel(tt, result.model)
    const bottom = sentenceToProposition(tt, val(false))
    const propA = sentenceToProposition(tt, A)

    // ⊥ is always abnormal
    expect(model.isAbnormal(bottom)).toBe(true)

    // P(A | ⊥) = 1
    expect(model.conditionalProbability(propA, bottom)).toBe(1)
  }, 30000)

  test('P(A ∧ B | A) + P(A ∧ ¬B | A) = 1', async () => {
    const constraints: Constraint[] = [
      gt(pr(A), lit(0))  // Make A normal
    ]
    const tt = new TruthTable(variables_in_constraints(constraints))
    const result = await solveLPS(solver, tt, constraints, 2)

    expect(result.status).toBe('sat')
    if (result.status !== 'sat') return

    const model = lpsModelToPopperModel(tt, result.model)
    const propA = sentenceToProposition(tt, A)
    const propAB = sentenceToProposition(tt, and(A, B))
    const propANotB = sentenceToProposition(tt, and(A, not(B)))

    const prob1 = model.conditionalProbability(propAB, propA) ?? 1
    const prob2 = model.conditionalProbability(propANotB, propA) ?? 1

    // P(A∧B | A) + P(A∧¬B | A) = 1
    expect(prob1 + prob2).toBeCloseTo(1, 10)
  }, 30000)
})

describe('evaluateWithPopperModel', () => {
  test('evaluates simple probability', async () => {
    const constraints: Constraint[] = [
      eq(pr(A), lit(0.5))
    ]
    const tt = new TruthTable(variables_in_constraints(constraints))
    const result = await solveLPS(solver, tt, constraints, 2)

    expect(result.status).toBe('sat')
    if (result.status !== 'sat') return

    const model = lpsModelToPopperModel(tt, result.model)

    // Evaluate Pr(A | ⊤)
    const value = evaluateRealExpr(tt, model, pr(A))
    expect(value).toBeCloseTo(0.5, 5)
  }, 30000)

  test('evaluates constraint correctly', async () => {
    const constraints: Constraint[] = [
      gt(pr(A), lit(0.3))
    ]
    const tt = new TruthTable(variables_in_constraints(constraints))
    const result = await solveLPS(solver, tt, constraints, 2)

    expect(result.status).toBe('sat')
    if (result.status !== 'sat') return

    const model = lpsModelToPopperModel(tt, result.model)

    // The constraint Pr(A | ⊤) > 0.3 should evaluate to true
    const isTrue = evaluateConstraint(tt, model, gt(pr(A), lit(0.3)))
    expect(isTrue).toBe(true)
  }, 30000)

  test('evaluates arithmetic expressions', async () => {
    const constraints: Constraint[] = [
      eq(pr(A), lit(0.4)),
      eq(pr(B), lit(0.3))
    ]
    const tt = new TruthTable(variables_in_constraints(constraints))
    const result = await solveLPS(solver, tt, constraints, 2)

    expect(result.status).toBe('sat')
    if (result.status !== 'sat') return

    const model = lpsModelToPopperModel(tt, result.model)

    // Evaluate Pr(A) + Pr(B)
    const value = evaluateRealExpr(tt, model, plus(pr(A), pr(B)))
    expect(value).toBeCloseTo(0.7, 5)
  }, 30000)
})

/**
 * Lexicographic Probability System (LPS) Solver for PopperSAT
 *
 * A Popper function is represented as an LPS: a sequence of probability measures
 * (μ₁, μ₂, ..., μ_K) where K is the number of layers.
 *
 * For conditional probability P(φ | ψ):
 * - Find the first layer k where μ_k(ψ) > 0 (ψ is "normal" at layer k)
 * - Then P(φ | ψ) = μ_k(φ ∧ ψ) / μ_k(ψ)
 * - If no such layer exists, ψ is "abnormal" and P(φ | ψ) = 1 for all φ
 *
 * Division-free encoding: Instead of p = n/d, we encode n = p * d
 * where d = μ_k(ψ), n = μ_k(φ ∧ ψ), and p is the probability value.
 */

import { TruthTable } from "./pr_sat"
import { PrSat } from "./types"
import { Proposition, entails, conjoin, PopperModel } from "./popper"
import { WrappedSolver, WrappedSolverResult } from "./z3_integration"

type RealExpr = PrSat['RealExpr']
type Constraint = PrSat['Constraint']

/**
 * A layer assignment maps each conditioning event (as a proposition/set of states)
 * to the layer where it first has positive mass.
 *
 * Layer 0 means "abnormal" (zero mass at all layers).
 * Layers 1, 2, ..., K are the actual probability measure layers.
 */
export type LayerAssignment = Map<string, number>  // proposition key -> layer (0 = abnormal)

/**
 * Convert a Proposition (Set of state indices) to a string key for the LayerAssignment map.
 */
export function propositionKey(prop: Proposition): string {
  return Array.from(prop).sort((a, b) => a - b).join(',')
}

/**
 * Convert a string key back to a Proposition.
 */
export function keyToProposition(key: string): Proposition {
  if (key === '') return new Set<number>()
  return new Set(key.split(',').map(s => parseInt(s)))
}

/**
 * Extract all conditioning events (the "given" part of P(φ | ψ)) from constraints.
 * Returns a set of unique propositions (as DNFs/state sets).
 */
export function extractConditioningEvents(tt: TruthTable, constraints: Constraint[]): Proposition[] {
  const events = new Map<string, Proposition>()

  function processRealExpr(expr: RealExpr): void {
    if (expr.tag === 'given_probability') {
      // Convert the conditioning sentence to a proposition (set of states)
      const dnf = tt.compute_dnf(expr.given)
      const prop = new Set(dnf)
      const key = propositionKey(prop)
      if (!events.has(key)) {
        events.set(key, prop)
      }
      // Note: expr.arg is a Sentence, not a RealExpr, so no nested probabilities to process
    } else if (expr.tag === 'negative') {
      processRealExpr(expr.expr)
    } else if (expr.tag === 'plus' || expr.tag === 'minus' || expr.tag === 'multiply') {
      processRealExpr(expr.left)
      processRealExpr(expr.right)
    } else if (expr.tag === 'divide') {
      processRealExpr(expr.numerator)
      processRealExpr(expr.denominator)
    } else if (expr.tag === 'power') {
      processRealExpr(expr.base)
      processRealExpr(expr.exponent)
    }
    // literal, variable, state_variable_sum have no conditioning events
  }

  function processConstraint(c: Constraint): void {
    if (c.tag === 'negation') {
      processConstraint(c.constraint)
    } else if (c.tag === 'conjunction' || c.tag === 'disjunction') {
      processConstraint(c.left as Constraint)
      processConstraint(c.right as Constraint)
    } else if (c.tag === 'equal' || c.tag === 'not_equal' || c.tag === 'less_than' ||
               c.tag === 'less_than_or_equal' || c.tag === 'greater_than' || c.tag === 'greater_than_or_equal') {
      // Comparison constraints have RealExpr on left and right
      processRealExpr(c.left)
      processRealExpr(c.right)
    }
  }

  for (const constraint of constraints) {
    processConstraint(constraint)
  }

  return Array.from(events.values())
}

/**
 * Generate all possible layer assignments for the given conditioning events.
 *
 * For K layers, each event can be assigned to layers 0 (abnormal), 1, 2, ..., K.
 * This generates (K+1)^n assignments where n is the number of events.
 *
 * Note: This can be optimized later with pruning, but for now we enumerate all.
 */
export function* generateLayerAssignments(
  events: Proposition[],
  maxLayers: number
): Generator<LayerAssignment> {
  const n = events.length
  const base = maxLayers + 1  // 0 through maxLayers inclusive

  // Generate all combinations
  const total = Math.pow(base, n)

  for (let i = 0; i < total; i++) {
    const assignment = new Map<string, number>()
    let value = i

    for (let j = 0; j < n; j++) {
      const layer = value % base
      value = Math.floor(value / base)
      const key = propositionKey(events[j])
      assignment.set(key, layer)
    }

    yield assignment
  }
}

/**
 * Check if a layer assignment is consistent with basic constraints:
 * - ⊥ (empty set) must be abnormal (layer 0)
 * - ⊤ (all states) must be normal at layer 1
 * - If ψ ⊆ φ and ψ is normal at layer k, then φ must also be normal at layer ≤ k
 */
export function isConsistentAssignment(
  tt: TruthTable,
  events: Proposition[],
  assignment: LayerAssignment
): boolean {
  const nStates = tt.n_states()

  for (const event of events) {
    const key = propositionKey(event)
    const layer = assignment.get(key) ?? 0

    // ⊥ must be abnormal
    if (event.size === 0 && layer !== 0) {
      return false
    }

    // ⊤ must be normal at layer 1
    if (event.size === nStates && layer !== 1) {
      return false
    }

    // Subset consistency: if ψ ⊆ φ and ψ is normal, φ must be normal at same or earlier layer
    for (const other of events) {
      if (other === event) continue
      const otherKey = propositionKey(other)
      const otherLayer = assignment.get(otherKey) ?? 0

      // If event ⊆ other (event entails other)
      if (entails(event, other)) {
        // If event is normal at layer k, other must be normal at layer ≤ k
        if (layer > 0 && (otherLayer === 0 || otherLayer > layer)) {
          return false
        }
      }
    }
  }

  return true
}

/**
 * Result of the LPS solver.
 */
export type LPSSolverResult =
  | { status: 'sat', model: LPSModel }
  | { status: 'unsat' }
  | { status: 'unknown' }
  | { status: 'error', message: string }

/**
 * An LPS model containing the layer assignments and probability values.
 */
export type LPSModel = {
  /** Number of layers used */
  numLayers: number

  /** Layer assignment for each conditioning event */
  layerAssignment: LayerAssignment

  /** Probability values at each layer: layerValues[k][stateIndex] = μ_k(state) */
  layerValues: Map<number, Map<number, number>>

  /** Get P(φ | ψ) for propositions */
  conditionalProbability: (phi: Proposition, psi: Proposition) => number
}

/**
 * Create a PopperModel from an LPSModel for use in the UI.
 */
export function lpsModelToPopperModel(_tt: TruthTable, lpsModel: LPSModel): PopperModel {
  return {
    isAbnormal: (prop: Proposition) => {
      // A proposition is abnormal if it has zero mass at all layers
      // This is determined by checking if it's in the layer assignment as layer 0
      // or if it's ⊥ (empty set)
      if (prop.size === 0) return true

      const key = propositionKey(prop)
      const layer = lpsModel.layerAssignment.get(key)

      // If we have an explicit assignment, use it
      if (layer !== undefined) {
        return layer === 0
      }

      // Otherwise, compute based on layer values
      // A proposition is abnormal if μ_k(prop) = 0 for all k
      for (let k = 1; k <= lpsModel.numLayers; k++) {
        const layerVals = lpsModel.layerValues.get(k)
        if (layerVals) {
          let mass = 0
          for (const state of prop) {
            mass += layerVals.get(state) ?? 0
          }
          if (mass > 0) return false
        }
      }
      return true
    },

    conditionalProbability: (phi: Proposition, psi: Proposition) => {
      return lpsModel.conditionalProbability(phi, psi)
    }
  }
}

/**
 * Placeholder: Create a stub LPS model for testing.
 * This will be replaced with the actual solver output.
 */
export function createStubLPSModel(tt: TruthTable): LPSModel {
  const nStates = tt.n_states()
  const layerValues = new Map<number, Map<number, number>>()

  // Single layer with uniform distribution
  const layer1 = new Map<number, number>()
  for (let i = 0; i < nStates; i++) {
    layer1.set(i, 1 / nStates)
  }
  layerValues.set(1, layer1)

  return {
    numLayers: 1,
    layerAssignment: new Map(),
    layerValues,
    conditionalProbability: (phi: Proposition, psi: Proposition) => {
      // If psi is empty (⊥), it's abnormal -> return 1
      if (psi.size === 0) return 1

      // Compute P(phi | psi) = μ(phi ∩ psi) / μ(psi)
      const intersection = conjoin(phi, psi)
      const layer1Vals = layerValues.get(1)!

      let psiMass = 0
      for (const state of psi) {
        psiMass += layer1Vals.get(state) ?? 0
      }

      if (psiMass === 0) return 1  // Abnormal

      let intersectionMass = 0
      for (const state of intersection) {
        intersectionMass += layer1Vals.get(state) ?? 0
      }

      return intersectionMass / psiMass
    }
  }
}

// ============================================================================
// Z3 Constraint Generation for LPS
// ============================================================================

/**
 * Generate the variable name for a state variable at a given layer.
 * Format: a_k_s where k is the layer (1-indexed) and s is the state (1-indexed for display)
 */
export function layerStateVarName(layer: number, stateIndex: number): string {
  return `a_${layer}_${stateIndex + 1}`
}

/**
 * Generate SMTLIB declarations for layer state variables.
 */
export function generateLayerVarDeclarations(numLayers: number, numStates: number): string[] {
  const lines: string[] = []
  lines.push('(set-logic QF_NRA)')

  for (let k = 1; k <= numLayers; k++) {
    for (let s = 0; s < numStates; s++) {
      lines.push(`(declare-const ${layerStateVarName(k, s)} Real)`)
    }
  }

  return lines
}

/**
 * Generate non-negativity constraints for all layer variables.
 */
export function generateNonNegativityConstraints(numLayers: number, numStates: number): string[] {
  const lines: string[] = []

  for (let k = 1; k <= numLayers; k++) {
    for (let s = 0; s < numStates; s++) {
      lines.push(`(assert (>= ${layerStateVarName(k, s)} 0))`)
    }
  }

  return lines
}

/**
 * Generate normalization constraint: sum of state vars at each layer ≤ 1.
 * (We use ≤ 1 to allow for layers with total mass < 1)
 */
export function generateNormalizationConstraints(numLayers: number, numStates: number): string[] {
  const lines: string[] = []

  for (let k = 1; k <= numLayers; k++) {
    const vars = Array.from({ length: numStates }, (_, s) => layerStateVarName(k, s))
    lines.push(`(assert (<= (+ ${vars.join(' ')}) 1))`)
  }

  return lines
}

/**
 * Generate SMTLIB expression for the sum of state variables in a proposition at a given layer.
 */
export function propositionMassExpr(layer: number, prop: Proposition): string {
  if (prop.size === 0) {
    return '0'
  }
  const vars = Array.from(prop).map(s => layerStateVarName(layer, s))
  if (vars.length === 1) {
    return vars[0]
  }
  return `(+ ${vars.join(' ')})`
}

/**
 * Generate layer assignment constraints:
 * - For each event assigned to layer k > 0: μ_k(event) > 0
 * - For each event assigned to layer k > 1: μ_j(event) = 0 for j < k
 * - For events assigned to layer 0 (abnormal): μ_k(event) = 0 for all k
 */
export function generateLayerAssignmentConstraints(
  events: Proposition[],
  assignment: LayerAssignment,
  numLayers: number
): string[] {
  const lines: string[] = []

  for (const event of events) {
    const key = propositionKey(event)
    const layer = assignment.get(key) ?? 0

    if (layer === 0) {
      // Abnormal: zero mass at all layers
      for (let k = 1; k <= numLayers; k++) {
        lines.push(`(assert (= ${propositionMassExpr(k, event)} 0))`)
      }
    } else {
      // Normal at layer `layer`: positive mass at that layer
      lines.push(`(assert (> ${propositionMassExpr(layer, event)} 0))`)

      // Zero mass at all earlier layers
      for (let k = 1; k < layer; k++) {
        lines.push(`(assert (= ${propositionMassExpr(k, event)} 0))`)
      }
    }
  }

  return lines
}

/**
 * Transform a real expression to use division-free encoding.
 * P(φ | ψ) at layer k becomes: numerator_k / denominator_k
 * where numerator_k = μ_k(φ ∧ ψ) and denominator_k = μ_k(ψ)
 *
 * For the division-free encoding, we introduce fresh variables for each
 * conditional probability and add constraints: numerator = prob * denominator
 */
export function transformRealExprToSMTLIB(
  tt: TruthTable,
  expr: RealExpr,
  _events: Proposition[],  // Reserved for future use (e.g., caching)
  assignment: LayerAssignment,
  freshVarCounter: { count: number }
): { smtlib: string, extraConstraints: string[] } {
  const extras: string[] = []

  function transform(e: RealExpr): string {
    if (e.tag === 'literal') {
      return e.value.toString()
    } else if (e.tag === 'variable') {
      return e.id
    } else if (e.tag === 'given_probability') {
      // P(arg | given)
      const argDnf = tt.compute_dnf(e.arg)
      const givenDnf = tt.compute_dnf(e.given)
      const argProp = new Set(argDnf)
      const givenProp = new Set(givenDnf)

      // Find the layer for the conditioning event
      const givenKey = propositionKey(givenProp)
      const layer = assignment.get(givenKey) ?? 0

      if (layer === 0) {
        // Abnormal conditioning: P(anything | abnormal) = 1
        return '1'
      }

      // Compute φ ∧ ψ
      const intersection = conjoin(argProp, givenProp)

      // Division-free encoding: introduce fresh variable p, constrain n = p * d
      const probVar = `_p${freshVarCounter.count++}`
      const numerator = propositionMassExpr(layer, intersection)
      const denominator = propositionMassExpr(layer, givenProp)

      extras.push(`(declare-const ${probVar} Real)`)
      extras.push(`(assert (>= ${probVar} 0))`)
      extras.push(`(assert (<= ${probVar} 1))`)
      extras.push(`(assert (= ${numerator} (* ${probVar} ${denominator})))`)

      return probVar
    } else if (e.tag === 'negative') {
      return `(- ${transform(e.expr)})`
    } else if (e.tag === 'plus') {
      return `(+ ${transform(e.left)} ${transform(e.right)})`
    } else if (e.tag === 'minus') {
      return `(- ${transform(e.left)} ${transform(e.right)})`
    } else if (e.tag === 'multiply') {
      return `(* ${transform(e.left)} ${transform(e.right)})`
    } else if (e.tag === 'divide') {
      return `(/ ${transform(e.numerator)} ${transform(e.denominator)})`
    } else if (e.tag === 'power') {
      return `(^ ${transform(e.base)} ${transform(e.exponent)})`
    } else if (e.tag === 'state_variable_sum') {
      // This shouldn't appear in user constraints, but handle it anyway
      const vars = e.indices.map(s => layerStateVarName(1, s))
      if (vars.length === 0) return '0'
      if (vars.length === 1) return vars[0]
      return `(+ ${vars.join(' ')})`
    }
    throw new Error(`Unknown RealExpr tag: ${(e as any).tag}`)
  }

  return { smtlib: transform(expr), extraConstraints: extras }
}

/**
 * Transform a constraint to SMTLIB with division-free encoding.
 */
export function transformConstraintToSMTLIB(
  tt: TruthTable,
  constraint: Constraint,
  events: Proposition[],
  assignment: LayerAssignment,
  freshVarCounter: { count: number }
): { smtlib: string, extraConstraints: string[] } {
  const allExtras: string[] = []

  function transform(c: Constraint): string {
    if (c.tag === 'negation') {
      return `(not ${transform(c.constraint)})`
    } else if (c.tag === 'conjunction') {
      return `(and ${transform(c.left as Constraint)} ${transform(c.right as Constraint)})`
    } else if (c.tag === 'disjunction') {
      return `(or ${transform(c.left as Constraint)} ${transform(c.right as Constraint)})`
    } else if (c.tag === 'equal' || c.tag === 'not_equal' || c.tag === 'less_than' ||
               c.tag === 'less_than_or_equal' || c.tag === 'greater_than' || c.tag === 'greater_than_or_equal') {
      // Comparison constraint - left and right are RealExpr
      const { smtlib: leftSmt, extraConstraints: leftExtras } = transformRealExprToSMTLIB(tt, c.left, events, assignment, freshVarCounter)
      const { smtlib: rightSmt, extraConstraints: rightExtras } = transformRealExprToSMTLIB(tt, c.right, events, assignment, freshVarCounter)
      allExtras.push(...leftExtras, ...rightExtras)

      const opMap: Record<string, string> = {
        'equal': '=',
        'not_equal': 'distinct',
        'less_than': '<',
        'less_than_or_equal': '<=',
        'greater_than': '>',
        'greater_than_or_equal': '>='
      }
      const op = opMap[c.tag]

      return `(${op} ${leftSmt} ${rightSmt})`
    }
    throw new Error(`Unknown constraint tag: ${(c as any).tag}`)
  }

  return { smtlib: transform(constraint), extraConstraints: allExtras }
}

/**
 * Generate complete SMTLIB input for a given layer assignment.
 */
export function generateSMTLIBForAssignment(
  tt: TruthTable,
  constraints: Constraint[],
  events: Proposition[],
  assignment: LayerAssignment,
  numLayers: number
): string {
  const lines: string[] = []
  const numStates = tt.n_states()

  // Declarations
  lines.push(...generateLayerVarDeclarations(numLayers, numStates))

  // Basic constraints
  lines.push(...generateNonNegativityConstraints(numLayers, numStates))
  lines.push(...generateNormalizationConstraints(numLayers, numStates))

  // Layer assignment constraints
  lines.push(...generateLayerAssignmentConstraints(events, assignment, numLayers))

  // Transform user constraints
  const freshVarCounter = { count: 0 }
  for (const constraint of constraints) {
    const { smtlib, extraConstraints } = transformConstraintToSMTLIB(tt, constraint, events, assignment, freshVarCounter)
    lines.push(...extraConstraints)
    lines.push(`(assert ${smtlib})`)
  }

  lines.push('(check-sat)')
  lines.push('(get-model)')

  return lines.join('\n')
}

// ============================================================================
// Main LPS Solver
// ============================================================================

/**
 * Parse layer variable values from Z3 model output.
 * Variable names are in format: a_k_s where k is layer (1-indexed), s is state (1-indexed)
 */
export function parseLayerValuesFromAssignments(
  assignments: Record<string, number>,
  numLayers: number,
  _numStates: number  // Reserved for validation
): Map<number, Map<number, number>> {
  const layerValues = new Map<number, Map<number, number>>()

  for (let k = 1; k <= numLayers; k++) {
    layerValues.set(k, new Map<number, number>())
  }

  for (const [varName, value] of Object.entries(assignments)) {
    // Parse variable name: a_k_s
    const match = varName.match(/^a_(\d+)_(\d+)$/)
    if (match) {
      const layer = parseInt(match[1])
      const stateIndex = parseInt(match[2]) - 1  // Convert back to 0-indexed
      const layerMap = layerValues.get(layer)
      if (layerMap) {
        layerMap.set(stateIndex, value)
      }
    }
  }

  return layerValues
}

/**
 * Build an LPSModel from Z3 solver result.
 */
export function buildLPSModelFromResult(
  _tt: TruthTable,  // Reserved for future use
  assignment: LayerAssignment,
  layerValues: Map<number, Map<number, number>>,
  numLayers: number
): LPSModel {
  return {
    numLayers,
    layerAssignment: assignment,
    layerValues,
    conditionalProbability: (phi: Proposition, psi: Proposition) => {
      // If psi is empty (⊥), it's abnormal -> return 1
      if (psi.size === 0) return 1

      // Find the layer for psi
      const psiKey = propositionKey(psi)
      const layer = assignment.get(psiKey)

      // If psi is abnormal (layer 0 or not found with zero mass), return 1
      if (layer === 0) return 1

      // Find first layer where psi has positive mass
      let psiLayer = layer
      if (psiLayer === undefined) {
        // Not in assignment, compute from layer values
        for (let k = 1; k <= numLayers; k++) {
          const layerVals = layerValues.get(k)
          if (layerVals) {
            let mass = 0
            for (const state of psi) {
              mass += layerVals.get(state) ?? 0
            }
            if (mass > 0) {
              psiLayer = k
              break
            }
          }
        }
      }

      if (psiLayer === undefined) return 1  // Abnormal

      // Compute P(phi | psi) = μ_k(phi ∩ psi) / μ_k(psi)
      const intersection = conjoin(phi, psi)
      const layerVals = layerValues.get(psiLayer)

      if (!layerVals) return 1  // Shouldn't happen

      let psiMass = 0
      for (const state of psi) {
        psiMass += layerVals.get(state) ?? 0
      }

      if (psiMass === 0) return 1  // Abnormal at this layer

      let intersectionMass = 0
      for (const state of intersection) {
        intersectionMass += layerVals.get(state) ?? 0
      }

      return intersectionMass / psiMass
    }
  }
}

/**
 * Main LPS solver function.
 *
 * Algorithm:
 * 1. Extract conditioning events from constraints
 * 2. For each layer assignment (up to maxLayers):
 *    a. Check basic consistency
 *    b. Generate QF_NRA constraints with division-free encoding
 *    c. Call Z3
 *    d. If SAT, extract model and return
 * 3. If all assignments fail, return UNSAT
 */
export async function solveLPS(
  solver: WrappedSolver,
  tt: TruthTable,
  constraints: Constraint[],
  maxLayers: number = 2,
  abortSignal?: AbortSignal
): Promise<LPSSolverResult> {
  const events = extractConditioningEvents(tt, constraints)
  console.log(`LPS Solver: Found ${events.length} conditioning events`)
  console.log(`LPS Solver: Max layers = ${maxLayers}`)

  // Add ⊤ (tautology) to events if not present - it must be normal at layer 1
  const allStates = new Set(Array.from({ length: tt.n_states() }, (_, i) => i))
  const topKey = propositionKey(allStates)
  if (!events.some(e => propositionKey(e) === topKey)) {
    events.push(allStates)
  }

  // Count total assignments to try
  let totalAssignments = 0
  let validAssignments = 0
  let testedAssignments = 0

  for (const assignment of generateLayerAssignments(events, maxLayers)) {
    // Check for abort
    if (abortSignal?.aborted) {
      return { status: 'error', message: 'Cancelled' }
    }

    totalAssignments++

    if (!isConsistentAssignment(tt, events, assignment)) {
      continue
    }
    validAssignments++

    // Generate SMTLIB
    const smtlib = generateSMTLIBForAssignment(tt, constraints, events, assignment, maxLayers)
    console.log(`LPS Solver: Testing assignment ${testedAssignments + 1}/${validAssignments}`)
    testedAssignments++

    // Call Z3
    const result: WrappedSolverResult = await solver.solve(smtlib, abortSignal)

    if (result.status === 'sat') {
      console.log(`LPS Solver: SAT found at assignment ${testedAssignments}`)

      // Extract layer values from the model using named_assignments
      // Variable names are in format a_k_s where k is layer, s is state (1-indexed)
      const layerValues = new Map<number, Map<number, number>>()
      for (let k = 1; k <= maxLayers; k++) {
        layerValues.set(k, new Map<number, number>())
      }

      for (const [varName, value] of Object.entries(result.named_assignments)) {
        // Parse variable name: a_k_s (layer k, state s, both 1-indexed)
        const match = varName.match(/^a_(\d+)_(\d+)$/)
        if (match) {
          const layer = parseInt(match[1])
          const stateIndex = parseInt(match[2]) - 1  // Convert to 0-indexed
          const layerMap = layerValues.get(layer)
          if (layerMap) {
            layerMap.set(stateIndex, value)
          }
        }
      }

      // Fill in any missing values with 0
      for (let k = 1; k <= maxLayers; k++) {
        const layerMap = layerValues.get(k)!
        for (let s = 0; s < tt.n_states(); s++) {
          if (!layerMap.has(s)) {
            layerMap.set(s, 0)
          }
        }
      }

      const model = buildLPSModelFromResult(tt, assignment, layerValues, maxLayers)

      console.log(`LPS Solver: ${totalAssignments} total, ${validAssignments} consistent, ${testedAssignments} tested`)
      return { status: 'sat', model }

    } else if (result.status === 'cancelled') {
      return { status: 'error', message: 'Cancelled' }

    } else if (result.status === 'exception') {
      console.error(`LPS Solver: Z3 exception: ${result.message}`)
      // Continue to next assignment
    }
    // For 'unsat' and 'unknown', continue to next assignment
  }

  console.log(`LPS Solver: ${totalAssignments} total, ${validAssignments} consistent, ${testedAssignments} tested - UNSAT`)

  return { status: 'unsat' }
}

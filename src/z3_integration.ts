import { Arith, Bool, Context, Expr, init, Model, Z3HighLevel, Z3LowLevel } from "z3-solver"
import { match_s, S, spv, clause, s_to_string, default_clause } from "./s"
import { constraints_to_smtlib_lines, eliminate_state_variable_index, enrich_constraints, parse_s, real_expr_to_smtlib, translate, TruthTable, variables_in_constraints, state_index_id, constraint_to_smtlib, translate_constraint, translate_real_expr, free_variables_in_constraint_or_real_expr as free_sentence_variables_in_constraint_or_real_expr, LetterSet, free_real_variables_in_constraint_or_real_expr, VariableLists, div0_conditions_in_constraint_or_real_expr, translate_constraint_or_real_expr, eliminate_state_variable_index_in_constraint_or_real_expr } from "./pr_sat"
import { ConstraintOrRealExpr, PrSat } from "./types"
import { as_array, assert, assert_exists, assert_result, fallthrough, Res, sleep } from "./utils"

type RealExpr = PrSat['RealExpr']
type Constraint = PrSat['Constraint']

export const init_z3 = async (): Promise<Z3HighLevel & Z3LowLevel> => {
    // console.log('Initializing z3...')
    // const init_start = performance.now()
    const z3_interface = await init()
    // const init_end = performance.now()
    // console.log('done!')
    // console.log(`init time: ${(init_end - init_start) / 1000} seconds.`)
    return z3_interface
}

// const model_to_state_values = async <CtxKey extends string>(ctx: Context<CtxKey>, model: Model<CtxKey>): Promise<Record<number, number>> => {
//   const values_map: Record<number, number> = {}
//   const { simplify } = ctx
//   for (const decl of model.decls()) {
//     if (decl.arity() !== 0) {
//       // throw new Error(`model includes a function declaration with arity not equal to zero!\nname: ${decl.name()}`)
//       continue
//     }
//     const name = decl.name().toString()
//     if (name.length < 3) {
//       throw new Error(`Expected model entry name to be of length at least 3!\nname: ${name.length}`)
//     }
//     const index_str = name.substring(2)
//     const index = parseInt(index_str)
//     if (isNaN(index)) {
//       throw new Error(`Expected model entry name to be of the form s_<number>!\nname: ${name}`)
//     }

//     const value_expr = await simplify(model.eval(decl.call()))
//     const parsed_s = parse_s(value_expr.sexpr())
//     const value = parse_and_evaluate(parsed_s)
//     values_map[index] = value
//   }

//   const values: number[] = []
//   for (let i = 0; i < Object.keys(values_map).length; i++) {
//     values.push(values_map[i])
//   }
//   return values
// }

export type ModelAssignmentOutput =
  | { tag: 'literal', value: number }
  | { tag: 'negative', inner: ModelAssignmentOutput }
  | { tag: 'rational', numerator: ModelAssignmentOutput, denominator: ModelAssignmentOutput }
  | { tag: 'surd', a: ModelAssignmentOutput, b: ModelAssignmentOutput, c: number }  // a + b√c
  | { tag: 'root-obj', index: number, a: ModelAssignmentOutput, b: ModelAssignmentOutput, c: ModelAssignmentOutput }
  | { tag: 'generic-root-obj', index: number, degree: number, coefficients: number[] }
  | { tag: 'unknown', s: S }

export const constraint_or_real_expr_to_smtlib = (tt: TruthTable, c_or_re: ConstraintOrRealExpr): S => {
  if (c_or_re.tag === 'constraint') {
    const t = translate_constraint(tt, c_or_re.constraint)
    return constraint_to_smtlib(t)
  } else if (c_or_re.tag === 'real_expr') {
    const t = translate_real_expr(tt, c_or_re.real_expr)
    return real_expr_to_smtlib(t)
  } else {
    return fallthrough('constraint_or_real_expr_to_smtlib', c_or_re)
  }
}

export type FancyEvaluatorOutput =
  | { tag: 'undeclared-vars', variables: VariableLists }
  | { tag: 'div0' }
  | { tag: 'result', result: ModelAssignmentOutput }
  | { tag: 'bool-result', result: boolean }

// const constraint_contains_div0 = (c: Constraint): boolean => {
//   const sub = constraint_contains_div0
//   const sub_real = real_expr_contains_div0
//   if (c.tag === 'biconditional') {
//     return sub(c.left) || sub(c.right)
//   } else if (c.tag === 'conditional') {
//     return sub(c.left) || sub(c.right)
//   } else if (c.tag === 'conjunction') {
//     return sub(c.left) || sub(c.right)
//   } else if (c.tag === 'disjunction') {
//     return sub(c.left) || sub(c.right)
//   } else if (c.tag === 'equal') {
//     return sub_real(c.left) || sub_real(c.right)
//   } else if (c.tag === 'greater_than') {
//     return sub_real(c.left) || sub_real(c.right)
//   } else if (c.tag === 'greater_than_or_equal') {
//     return sub_real(c.left) || sub_real(c.right)
//   } else if (c.tag === 'less_than') {
//     return sub_real(c.left) || sub_real(c.right)
//   } else if (c.tag === 'less_than_or_equal') {
//     return sub_real(c.left) || sub_real(c.right)
//   } else if (c.tag === 'negation') {
//     return sub(c.constraint)
//   } else if (c.tag === 'not_equal') {
//     return sub_real(c.left) || sub_real(c.right)
//   } else {
//     return fallthrough('constraint_contains_div0', c)
//   }
// }

// const real_expr_contains_div0 = (e: RealExpr): boolean => {
//   if (e.tag === 'divide') {
//     return 
//   } else if (e.tag === 'given_probability') {
//   } else if (e.tag === 'literal') {
//   } else if (e.tag === 'minus') {
//   } else if (e.tag === 'multiply') {
//   } else if (e.tag === 'negative') {
//   } else if (e.tag === 'plus') {
//   } else if (e.tag === 'power') {
//   } else if (e.tag === 'probability') {
//   } else if (e.tag === 'state_variable_sum') {
//   } else if (e.tag === 'variable') {
//   } else {
//     return fallthrough('real_expr_contains_div0', e)
//   }
// }

// const constraint_or_real_expr_contains_div0 = (c_or_re: ConstraintOrRealExpr): boolean => {
//   if (c_or_re.tag === 'constraint') {
//     return constraint_contains_div0(c_or_re.constraint)
//   } else if (c_or_re.tag === 'real_expr') {
//     return real_expr_contains_div0(c_or_re.real_expr)
//   } else {
//     return fallthrough('constraint_or_real_expr_contains_div0', c_or_re)
//   }
// }

// The given Solver should already have all the other variables inside it declared but if not I will CRY.
export const fancy_evaluate_constraint_or_real_expr = async <CtxKey extends string>(ctx: Context<CtxKey>, model: Model<CtxKey>, tt: TruthTable, c_or_re: ConstraintOrRealExpr): Promise<FancyEvaluatorOutput> => {
  const free_sentence_vars = free_sentence_variables_in_constraint_or_real_expr(c_or_re, new LetterSet(), new LetterSet([...tt.letters()]))
  const free_real_vars = free_real_variables_in_constraint_or_real_expr(c_or_re, new Set)

  if (!free_sentence_vars.is_empty() || free_real_vars.size > 0) {
    return { tag: 'undeclared-vars', variables: { sentence: [...free_sentence_vars], real: [...free_real_vars] } }
  }

  const div0_constraints = div0_conditions_in_constraint_or_real_expr(c_or_re)
  const index_to_eliminate = tt.n_states() - 1  // TODO: put this in a function.
  for (const c of div0_constraints) {
    const translated = translate_constraint(tt, c)
    const [_, eliminated] = eliminate_state_variable_index_in_constraint_or_real_expr(tt.n_states(), index_to_eliminate, { tag: 'constraint', constraint: translated })
    if (eliminated.tag !== 'constraint') throw new Error('Expected constraint after elimination')
    const z3_expr = constraint_to_bool(ctx, model, eliminated.constraint)
    const result = model.eval(z3_expr, true)  // true = model_completion to evaluate eliminated variables
    if (result.sexpr() === 'false') {
      // found a denominator equal to zero!
      return { tag: 'div0' }
    }
  }

  const translated_c_or_re = translate_constraint_or_real_expr(tt, c_or_re)
  const [_, eliminated] = eliminate_state_variable_index_in_constraint_or_real_expr(tt.n_states(), index_to_eliminate, translated_c_or_re)
  const to_evaluate_z3 = constraint_or_real_expr_to_z3_expr(ctx, model, eliminated)
  if (c_or_re.tag === 'constraint') {
    const result = model.eval(to_evaluate_z3, true)
    const s = result.sexpr()
    return { tag: 'bool-result', result: s === 'true' }
  }

  const output = await expr_to_assignment(ctx, model, to_evaluate_z3)
  console.log('RESULT', output)

  return { tag: 'result', result: output }
}

const int_to_s = (i: number): S => {
  if (i < 0) {
    return ['-', (-i).toString()]
  } else {
    return i.toString()
  }
}

export const poly_s = (cs: number[]) => {
  if (cs.length === 0) {
    return '0'
  } else if (cs.length === 1) {
    return int_to_s(cs[0]).toString()
  } else if (cs.length === 2) {
    return ['+', ['*', int_to_s(cs[0]), 'x'], cs[1].toString()]
  } else {
    const ret: S = ['+']
    for (const [index, c] of cs.entries()) {
      const exp = cs.length - index - 1
      if (exp === 0) {
        ret.push(int_to_s(c))
      } else if (exp === 1) {
        if (c === 1) {
          ret.push('x')
        } else if (c === 0) {
          // skip!
        } else {
          ret.push(['*', int_to_s(c), 'x'])
        }
      } else {
        if (c === 1) {
          ret.push(['^', 'x', exp.toString()])
        } else if (c === -1) {
          ret.push(['-', ['^', 'x', exp.toString()]])
        } else if (c === 0) {
          // skip!
        } else {
          ret.push(['*', int_to_s(c), ['^', 'x', exp.toString()]])
        }
      }
    }
    return ret
  }
}

export const model_assignment_output_to_string = (output: ModelAssignmentOutput): string => {
  const sub = (output: ModelAssignmentOutput): string => model_assignment_output_to_string(output)
  const wrap = (output: ModelAssignmentOutput, extra_wraps: ModelAssignmentOutput['tag'][] = []): string => {
    if (output.tag === 'literal' || output.tag === 'negative' || extra_wraps.includes(output.tag)) {
      return sub(output)
    } else {
      return `(${sub(output)})`
    }
  }

  if (output.tag === 'literal') {
    return output.value.toString()
  } else if (output.tag === 'negative') {
    return `-${wrap(output.inner)}`
  } else if (output.tag === 'rational') {
    return `${wrap(output.numerator)} / ${output.denominator}`
  } else if (output.tag === 'surd') {
    // a + b√c
    const aStr = sub(output.a)
    const bStr = sub(output.b)
    const sqrtStr = `√${output.c}`
    // Check if a is zero
    const aIsZero = output.a.tag === 'literal' && output.a.value === 0
    // Check if b is 1 or -1
    const bIsOne = output.b.tag === 'literal' && output.b.value === 1
    const bIsNegOne = output.b.tag === 'literal' && output.b.value === -1
    const bIsNeg = output.b.tag === 'negative' || bIsNegOne

    if (aIsZero) {
      if (bIsOne) return sqrtStr
      if (bIsNegOne) return `-${sqrtStr}`
      return `${bStr}${sqrtStr}`
    }
    if (bIsOne) return `${aStr} + ${sqrtStr}`
    if (bIsNegOne) return `${aStr} - ${sqrtStr}`
    if (bIsNeg) {
      // Handle negative b - show absolute value
      if (output.b.tag === 'negative') {
        return `${aStr} - ${wrap(output.b.inner)}${sqrtStr}`
      }
      // bIsNegOne already handled above
      return `${aStr} - ${bStr}${sqrtStr}`  // will show negative sign from bStr
    }
    return `${aStr} + ${bStr}${sqrtStr}`
  } else if (output.tag === 'root-obj') {
    return `(root-obj ${output.index} (${wrap(output.a)} * x^2 + ${wrap(output.b)} * x + ${wrap(output.c)}))`
  } else if (output.tag === 'generic-root-obj') {
    const terms_str = output.coefficients.map((c, index) => {
      const exp = output.coefficients.length - index
      if (exp === 0) {
        return c
      } else if (exp === 1) {
        return `${c} * x`
      } else if (exp >= 2) {
        return `${c} * x^${exp}`
      } else {
        throw new Error('fallthrough!')
      }
    }).join(' + ')
    return `(root-obj ${output.index} (${terms_str}))`
  } else if (output.tag === 'unknown') {
    return s_to_string(output.s, false)
  } else {
    return fallthrough('model_assignment_output_to_string', output)
  }
}

// // Should be *mostly* simplified, but still might run into issues so this function is here just in case.
// const simplify_model_assignment_output = (output: ModelAssignmentOutput): ModelAssignmentOutput => {
//   throw new Error('unimplemented')
// }

const parse_int = (a: string): Res<number, string> => {
  const as_int = parseInt (a)
  if (isNaN(as_int)) {
    return [false, `Parsing '${a}' as int gave a NaN!`]
  } else {
    return [true, as_int]
  }
}

const parse_float = (a: string): Res<number, string> => {
  const as_float = parseFloat(a)
  if (isNaN(as_float)) {
    return [false, `Parsing '${a}' as float gave a NaN!`]
  } else {
    return [true, as_float]
  }
}

const parse_and_evaluate = (s: S): number => {
  const [a, b, c, d] = [spv('a'), spv('b'), spv('c'), spv('d')]
  return match_s(s, [
    clause<{ a: 'string' }, number>({ a: 'string' }, a, (m) => {
      return assert_result(parse_float(m('a')))
    }),
    clause<{ a: 'string' }, number>({ a: 'string' }, ['-', a], (m) => {
      return -parse_and_evaluate(m('a'))
    }),
    clause<{ a: 'string', b: 'string' }, number>({ a: 'string', b: 'string' }, ['/', a, b], (m) => {
      return parse_and_evaluate(m('a')) / parse_and_evaluate(m('b'))
    }),
    // expect(parse_s('(root-obj (+ (* 8 (^ x 2)) (* 6 x) (- 1)) 2)'))
    clause<{ a: 's', b: 's', c: 's', d: 'string' }, number>(
      { a: 's', b: 's', c: 's', d: 'string' },
      ['root-obj', ['+', ['*', a], ['*', b], c], d],
      (m) => {
        const af = parse_and_evaluate(m('a'))
        const bf = parse_and_evaluate(m('b'))
        const cf = parse_and_evaluate(m('c'))
        const di = assert_result(parse_int(m('d')))

        // (-b +- sqrt(b^2 - 4ac)) / 2a
        const det = bf * bf - 4 * af * cf
        if (det < 0) {
          throw new Error('Evaluated value to complex number oops!')
        } else if (di === 1) {
          return (-bf - Math.sqrt(det)) / (2 * af)
        } else if (di === 2) {
          return (-bf + Math.sqrt(det)) / (2 * af)
        } else {
          throw new Error(`Unrecognized root index ${di}!`)
        }
      }),
  ])
}

// const parse_s_integer = (term: S): number | undefined => {
//   const a = spv('a')
//   return match_s(term, [
//     clause({ a: 'string' }, ['-', a], (m) => {
//       return -assert_result(parse_int(m('a')))
//     }),
//     clause({ a: 'string' }, a, (m) => {
//       return assert_result(parse_int(m('a')))
//     }),
//   ])
// }

// [number, integer]
const parse_poly_term = (term: S): [number, number] => {
  const c = spv('c')
  const exp = spv('exp')
  const pi = (s: string): number => assert_result(parse_int(s))
  return match_s(term, [
    clause<{ c: 'string' }, [number, number]>({ c: 'string' }, c, (m) => {
      const [is_int, as_int] = parse_int(m('c'))
      if (is_int) {
        return [as_int, 0]
      } else {
        // Then we just saw an 'x' and we should return 1 for both the coefficient and the degree.
        return [1, 1]
      }
    }),
    clause<{ c: 'string' }, [number, number]>({ c: 'string' }, ['-', c], (m) => {
      const [is_int, as_int] = parse_int(m('c'))
      if (is_int) {
        return [-as_int, 0]
      } else {
        return [-1, 1]
      }
    }),
    clause<{ exp: 'string' }, [number, number]>({ exp: 'string' }, ['^', 'x', exp], (m) => {
      return [1, pi(m('exp'))]
    }),
    clause<{ exp: 'string' }, [number, number]>({ exp: 'string' }, ['-', ['^', 'x', exp]], (m) => {
      return [-1, pi(m('exp'))]
    }),
    clause<{ c: 'string' }, [number, number]>({ c: 'string' }, ['*', c, 'x'], (m) => {
      return [pi(m('c')), 1]
    }),
    clause<{ c: 'string' }, [number, number]>({ c: 'string' }, ['*', ['-', c], 'x'], (m) => {
      return [-pi(m('c')), 1]
    }),
    clause<{ c: 'string', exp: 'string' }, [number, number]>({ c: 'string', exp: 'string' }, ['*', c, ['^', 'x', exp]], (m) => {
      return [pi(m('c')), assert_result(parse_int(m('exp')))]
    }),
    clause<{ c: 'string', exp: 'string' }, [number, number]>({ c: 'string', exp: 'string' }, ['*', ['-', c], ['^', 'x', exp]], (m) => {
      return [-pi(m('c')), assert_result(parse_int(m('exp')))]
    }),
  ])
}

export const parse_to_assignment = (s: S): ModelAssignmentOutput => {
  // const [a, b, c, d] = [spv('a'), spv('b'), spv('c'), spv('d')]
  const [a, b] = [spv('a'), spv('b')]
  return match_s(s, [
    clause<{ a: 'string' }, ModelAssignmentOutput>({ a: 'string' }, a, (m) => {
      const ma = m('a')
      const as_float = assert_result(parse_float(ma))
      return { tag: 'literal', value: as_float }
    }),
    clause<{ a: 's' }, ModelAssignmentOutput>({ a: 's' }, ['-', a], (m) => {
      const inner = parse_to_assignment(m('a'))
      return { tag: 'negative', inner }
    }),
    clause<{ a: 'string', b: 'string' }, ModelAssignmentOutput>({ a: 'string', b: 'string' }, ['/', a, b], (m) => {
      const numerator = parse_to_assignment(m('a'))
      const denominator = parse_to_assignment(m('b'))
      return { tag: 'rational', numerator, denominator }
    }),
    clause<{ a: 'string', b: 'string' }, ModelAssignmentOutput>({ a: 'string', b: 'string' }, ['/', a, b], (m) => {
      const numerator = parse_to_assignment(m('a'))
      const denominator = parse_to_assignment(m('b'))
      return { tag: 'rational', numerator, denominator }
    }),
    // clause<{ a: 's', b: 's', c: 's', d: 'string' }, ModelAssignmentOutput>(
    //   { a: 's', b: 's', c: 's', d: 'string' },
    //   ['root-obj', ['+', ['*', a, ['^', 'x', '2']], ['*', b], c], d],
    //   (m) => {
    //     const af = parse_to_assignment(m('a'))
    //     const bf = parse_to_assignment(m('b'))
    //     const cf = parse_to_assignment(m('c'))
    //     const di = assert_result(parse_int(m('d')))

    //     return { tag: 'root-obj', index: di, a: af, b: bf, c: cf }
    //   }),
      default_clause<ModelAssignmentOutput>((s) => {
        const t = s('s')
        if (Array.isArray(t) && t.length > 2 && t[0] === 'root-obj') {
          // super-hacky but it's fine.
          // it's of the form
          // ['root-obj', ['+'], index]
          const sum_s = assert_exists(as_array(t[1]), 'missing sum in root-obj!')
          if (sum_s.length <= 1) {
            throw new Error('sum_s in root-obj doesn\'t have enough terms!')
          }
          assert(sum_s[0] === '+', `first element of sum isn\'t '+', but is instead '${sum_s[0]}'!`)

          const coefficients: number[] = []
          const n_terms = sum_s.length - 1  // -1 to exclude leading '+'.
          let largest_exp = 0
          let previous_exp: number | undefined = undefined
          for (let term_index = 0; term_index < n_terms; term_index++) {
            const term = assert_exists(sum_s[1 + term_index], `term missing at index ${1 + term_index!}`)
            const [c, exp] = parse_poly_term(term)
            if (previous_exp !== undefined && previous_exp <= exp) {
              throw new Error('Expected exponents to monotonically decrease in polynomial!')
            }

            assert(previous_exp === undefined || previous_exp > exp)
            if (previous_exp !== undefined) {
              for (let exp_gap = previous_exp - 1; exp_gap > exp; exp_gap--) {
                coefficients.push(0)
              }
            }
            coefficients.push(c)

            largest_exp = Math.max(largest_exp, exp)
            previous_exp = exp
          }
          
          const index_s = assert_exists(t[2], 'missing index!')
          const index = typeof index_s === 'string' ? assert_result(parse_int(index_s))
            : typeof index_s === 'number' ? index_s
            : -1
          return { tag: 'generic-root-obj', degree: largest_exp, coefficients, index }
        } else {
          return { tag: 'unknown', s: s('s') }
        }
      })
  ])
}

export const model_assignment_output_to_s = (output: ModelAssignmentOutput): S => {
  const sub = (output: ModelAssignmentOutput): S => model_assignment_output_to_s(output)
  if (output.tag === 'literal') {
    return output.value.toString()
  } else if (output.tag === 'negative') {
    return ['-', sub(output.inner)]
  } else if (output.tag === 'rational') {
    return ['/', sub(output.numerator), sub(output.denominator)]
  } else if (output.tag === 'surd') {
    // Represent as (+ a (* b (sqrt c)))
    return ['+', sub(output.a), ['*', sub(output.b), ['sqrt', output.c.toString()]]]
  } else if (output.tag === 'root-obj') {
    return ['root-obj', ['+', ['*', sub(output.a), ['^', 'x', '2']], ['*', sub(output.b), 'x'], sub(output.c)], '2']
  } else if (output.tag === 'generic-root-obj') {
    const terms = output.coefficients.map((c, index) => {
      const exp = output.coefficients.length - index
      if (exp === 0) {
        return c
      } else if (exp === 1) {
        return ['*', c, 'x']
      } else if (exp >= 2) {
        // return `${c} * x^${exp}`
        return ['*', c, ['^', 'x', exp]]
      } else {
        throw new Error('fallthrough!')
      }
    })
    return ['root-obj', ['+', ...terms], output.index]
  } else if (output.tag === 'unknown') {
    return output.s
  } else {
    return fallthrough('model_assignment_output_to_s', output)
  }
}

const expr_to_assignment = async <CtxKey extends string>(ctx: Context<CtxKey>, model: Model<CtxKey>, expr: Expr<CtxKey>): Promise<ModelAssignmentOutput> => {
  const value_expr = await ctx.simplify(model.eval(expr))
  // const value_expr = await ctx.simplify(ctx.Real.val(-2138))
  const parsed_s = parse_s(value_expr.sexpr())
  const value = parse_to_assignment(parsed_s)
  return value
}

export const model_to_assigned_exprs = async <CtxKey extends string>(ctx: Context<CtxKey>, model: Model<CtxKey>): Promise<[number, Expr<CtxKey>][]> => {
  const assigned_exprs: [number, Expr<CtxKey>][] = []
  for (const decl of model.decls()) {
    if (decl.arity() !== 0) {
      // throw new Error(`model includes a function declaration with arity not equal to zero!\nname: ${decl.name()}`)
      continue
    }
    const name = decl.name().toString()

    // Only handle variables in format a_<number> (e.g., a_1, a_2)
    // Skip other variables like a_k_s (LPS format) or _p0 (fresh variables)
    const match = name.match(/^a_(\d+)$/)
    if (!match) {
      continue  // Skip non-matching variable names
    }

    const parsed_index = parseInt(match[1])
    // Variable names are 1-indexed (a_1, a_2, ...) but internal indices are 0-indexed
    const index = parsed_index - 1

    assigned_exprs.push([index, await ctx.simplify(model.eval(decl.call()))])
  }

  return assigned_exprs
}

// ============================================================================
// Exact Number Support (Rational or Float fallback for irrationals)
// ============================================================================

/**
 * A rational number represented as numerator/denominator.
 * Always kept in reduced form with positive denominator.
 */
export type Rational = {
  numer: bigint
  denom: bigint
}

/**
 * A quadratic surd: a + b√c where a, b are rationals and c is a non-negative integer.
 * When c=0 or b=0, this reduces to just the rational a.
 * The radicand c is kept in simplified form (no perfect square factors).
 */
export type QuadraticSurd = {
  a: Rational      // rational part
  b: Rational      // coefficient of √c
  c: bigint        // radicand (non-negative, square-free)
}

/**
 * An exact number: rational, quadratic surd, or float.
 * When both operands are rational, arithmetic stays rational.
 * When operands are surds with same radicand, result is a surd.
 * Falls back to float for incompatible surds or transcendental results.
 */
export type ExactNumber =
  | { tag: 'rational', value: Rational }
  | { tag: 'surd', value: QuadraticSurd }
  | { tag: 'float', value: number }

/** Compute GCD of two bigints */
function gcd(a: bigint, b: bigint): bigint {
  a = a < 0n ? -a : a
  b = b < 0n ? -b : b
  while (b !== 0n) {
    const t = b
    b = a % b
    a = t
  }
  return a
}

/** Create a reduced rational from numerator and denominator */
export function rational(numer: bigint, denom: bigint): Rational {
  if (denom === 0n) throw new Error('Rational: denominator cannot be zero')
  // Normalize sign: denominator always positive
  if (denom < 0n) {
    numer = -numer
    denom = -denom
  }
  // Reduce to lowest terms
  const g = gcd(numer, denom)
  return { numer: numer / g, denom: denom / g }
}

/** Create a rational from an integer */
export function rationalFromInt(n: bigint | number): Rational {
  return { numer: BigInt(n), denom: 1n }
}

/** The rational number 0 */
export const RATIONAL_ZERO: Rational = { numer: 0n, denom: 1n }

/** The rational number 1 */
export const RATIONAL_ONE: Rational = { numer: 1n, denom: 1n }

/** Add two rationals */
export function rationalAdd(a: Rational, b: Rational): Rational {
  return rational(a.numer * b.denom + b.numer * a.denom, a.denom * b.denom)
}

/** Multiply two rationals */
export function rationalMul(a: Rational, b: Rational): Rational {
  return rational(a.numer * b.numer, a.denom * b.denom)
}

/** Divide two rationals (a / b) */
export function rationalDiv(a: Rational, b: Rational): Rational {
  if (b.numer === 0n) throw new Error('Rational: division by zero')
  return rational(a.numer * b.denom, a.denom * b.numer)
}

/** Check if a rational equals zero */
export function rationalIsZero(r: Rational): boolean {
  return r.numer === 0n
}

/** Check if two rationals are equal */
export function rationalEquals(a: Rational, b: Rational): boolean {
  return a.numer === b.numer && a.denom === b.denom
}

/** Convert rational to float */
export function rationalToFloat(r: Rational): number {
  return Number(r.numer) / Number(r.denom)
}

/** Format a rational as a string "n/d" or just "n" if d=1 */
export function rationalToString(r: Rational): string {
  if (r.denom === 1n) return r.numer.toString()
  return `${r.numer}/${r.denom}`
}

// --- QuadraticSurd utilities ---

/**
 * Extract the largest perfect square factor from n.
 * Returns [k, m] where n = k² * m and m is square-free.
 */
function extractSquareFactor(n: bigint): [bigint, bigint] {
  if (n <= 1n) return [1n, n]

  let k = 1n
  let m = n

  // Check small primes
  const primes = [2n, 3n, 5n, 7n, 11n, 13n, 17n, 19n, 23n, 29n, 31n]
  for (const p of primes) {
    while (m % (p * p) === 0n) {
      k *= p
      m /= (p * p)
    }
  }

  // For larger factors, just do trial division up to sqrt(m)
  let i = 37n
  while (i * i <= m) {
    while (m % (i * i) === 0n) {
      k *= i
      m /= (i * i)
    }
    i += 2n
  }

  return [k, m]
}

/**
 * Create a simplified quadratic surd a + b√c.
 * Extracts perfect square factors from c and absorbs them into b.
 * If c becomes 1 or b becomes 0, the surd collapses to rational.
 */
export function surd(a: Rational, b: Rational, c: bigint): QuadraticSurd {
  if (c < 0n) throw new Error('Surd: radicand must be non-negative')

  // If b = 0 or c = 0, the surd part vanishes
  if (rationalIsZero(b) || c === 0n) {
    return { a, b: RATIONAL_ZERO, c: 0n }
  }

  // Extract perfect square factors: c = k² * m
  const [k, m] = extractSquareFactor(c)

  // √c = √(k²m) = k√m, so b√c = (b*k)√m
  const newB = rationalMul(b, rationalFromInt(k))

  // If m = 1, √m = 1, so the surd collapses to rational
  if (m === 1n) {
    return { a: rationalAdd(a, newB), b: RATIONAL_ZERO, c: 0n }
  }

  return { a, b: newB, c: m }
}

/** Create a surd from just a rational (no irrational part) */
export function surdFromRational(r: Rational): QuadraticSurd {
  return { a: r, b: RATIONAL_ZERO, c: 0n }
}

/** Check if a surd is actually just a rational (b=0 or c=0) */
export function surdIsRational(s: QuadraticSurd): boolean {
  return rationalIsZero(s.b) || s.c === 0n
}

/** Convert a surd to a rational if possible, otherwise undefined */
export function surdToRational(s: QuadraticSurd): Rational | undefined {
  if (surdIsRational(s)) return s.a
  return undefined
}

/** Convert a surd to float */
export function surdToFloat(s: QuadraticSurd): number {
  return rationalToFloat(s.a) + rationalToFloat(s.b) * Math.sqrt(Number(s.c))
}

/** Add two surds (only exact if same radicand or one is rational) */
export function surdAdd(x: QuadraticSurd, y: QuadraticSurd): QuadraticSurd | undefined {
  // If both are rational, just add
  if (surdIsRational(x) && surdIsRational(y)) {
    return surdFromRational(rationalAdd(x.a, y.a))
  }

  // If one is rational, add to the rational part
  if (surdIsRational(x)) {
    return surd(rationalAdd(x.a, y.a), y.b, y.c)
  }
  if (surdIsRational(y)) {
    return surd(rationalAdd(x.a, y.a), x.b, x.c)
  }

  // Both have irrational parts - only works if same radicand
  if (x.c === y.c) {
    return surd(rationalAdd(x.a, y.a), rationalAdd(x.b, y.b), x.c)
  }

  // Different radicands - cannot combine exactly
  return undefined
}

/** Subtract two surds */
export function surdSub(x: QuadraticSurd, y: QuadraticSurd): QuadraticSurd | undefined {
  const negY: QuadraticSurd = { a: { numer: -y.a.numer, denom: y.a.denom }, b: { numer: -y.b.numer, denom: y.b.denom }, c: y.c }
  return surdAdd(x, negY)
}

/** Multiply two surds (only exact if same radicand or one is rational) */
export function surdMul(x: QuadraticSurd, y: QuadraticSurd): QuadraticSurd | undefined {
  // (a + b√c)(d + e√f) = ad + ae√f + bd√c + be√(cf)
  // This only stays exact if c = f (or one is rational)

  if (surdIsRational(x)) {
    // x.a * (y.a + y.b√y.c) = x.a*y.a + x.a*y.b√y.c
    return surd(rationalMul(x.a, y.a), rationalMul(x.a, y.b), y.c)
  }
  if (surdIsRational(y)) {
    return surd(rationalMul(x.a, y.a), rationalMul(y.a, x.b), x.c)
  }

  // Both have irrational parts
  if (x.c === y.c) {
    // (a + b√c)(d + e√c) = (ad + bec) + (ae + bd)√c
    const ad = rationalMul(x.a, y.a)
    const bec = rationalMul(rationalMul(x.b, y.b), rationalFromInt(x.c))
    const ae = rationalMul(x.a, y.b)
    const bd = rationalMul(x.b, y.a)
    return surd(rationalAdd(ad, bec), rationalAdd(ae, bd), x.c)
  }

  // Different radicands
  return undefined
}

/** Divide two surds (only exact if same radicand or divisor is rational) */
export function surdDiv(x: QuadraticSurd, y: QuadraticSurd): QuadraticSurd | undefined {
  if (surdIsRational(y)) {
    if (rationalIsZero(y.a)) return undefined // division by zero
    return surd(rationalDiv(x.a, y.a), rationalDiv(x.b, y.a), x.c)
  }

  if (surdIsRational(x) && x.c === y.c) {
    // x / (d + e√c) = x(d - e√c) / (d² - e²c)
    // But x is rational so this simplifies
  }

  // (a + b√c) / (d + e√c) = (a + b√c)(d - e√c) / (d² - e²c)
  // Multiply by conjugate
  if (x.c === y.c || surdIsRational(x)) {
    const c = surdIsRational(x) ? y.c : x.c
    const conjugate: QuadraticSurd = { a: y.a, b: { numer: -y.b.numer, denom: y.b.denom }, c }

    // Denominator: (d + e√c)(d - e√c) = d² - e²c
    const d2 = rationalMul(y.a, y.a)
    const e2c = rationalMul(rationalMul(y.b, y.b), rationalFromInt(c))
    const denom = rationalAdd(d2, { numer: -e2c.numer, denom: e2c.denom })

    if (rationalIsZero(denom)) return undefined // division by zero

    // Numerator
    const xSurd: QuadraticSurd = surdIsRational(x) ? { a: x.a, b: RATIONAL_ZERO, c } : x
    const numer = surdMul(xSurd, conjugate)
    if (!numer) return undefined

    // Divide by rational denominator
    return surd(rationalDiv(numer.a, denom), rationalDiv(numer.b, denom), c)
  }

  return undefined
}

/** Negate a surd */
export function surdNeg(s: QuadraticSurd): QuadraticSurd {
  return { a: { numer: -s.a.numer, denom: s.a.denom }, b: { numer: -s.b.numer, denom: s.b.denom }, c: s.c }
}

/** Format a surd for display */
export function surdToString(s: QuadraticSurd): string {
  if (surdIsRational(s)) {
    return rationalToString(s.a)
  }

  const aStr = rationalToString(s.a)
  const bIsNeg = s.b.numer < 0n
  const absB: Rational = { numer: bIsNeg ? -s.b.numer : s.b.numer, denom: s.b.denom }
  const bStr = rationalEquals(absB, RATIONAL_ONE) ? '' : rationalToString(absB)
  const sqrtStr = `√${s.c}`

  if (rationalIsZero(s.a)) {
    // Just the surd part
    if (bIsNeg) {
      return bStr ? `-${bStr}${sqrtStr}` : `-${sqrtStr}`
    }
    return bStr ? `${bStr}${sqrtStr}` : sqrtStr
  }

  // Both parts
  if (bIsNeg) {
    return bStr ? `${aStr} - ${bStr}${sqrtStr}` : `${aStr} - ${sqrtStr}`
  }
  return bStr ? `${aStr} + ${bStr}${sqrtStr}` : `${aStr} + ${sqrtStr}`
}

// --- ExactNumber utilities ---

/** ExactNumber constants */
export const EXACT_ZERO: ExactNumber = { tag: 'rational', value: RATIONAL_ZERO }
export const EXACT_ONE: ExactNumber = { tag: 'rational', value: RATIONAL_ONE }

/** Create an ExactNumber from a rational */
export function exactFromRational(r: Rational): ExactNumber {
  return { tag: 'rational', value: r }
}

/** Create an ExactNumber from a surd */
export function exactFromSurd(s: QuadraticSurd): ExactNumber {
  // If it's actually rational, return as rational
  const r = surdToRational(s)
  if (r) return { tag: 'rational', value: r }
  return { tag: 'surd', value: s }
}

/** Create an ExactNumber from a float (for irrationals) */
export function exactFromFloat(f: number): ExactNumber {
  return { tag: 'float', value: f }
}

/** Convert ExactNumber to float */
export function exactToFloat(e: ExactNumber): number {
  if (e.tag === 'rational') return rationalToFloat(e.value)
  if (e.tag === 'surd') return surdToFloat(e.value)
  return e.value
}

/** Check if ExactNumber is zero */
export function exactIsZero(e: ExactNumber): boolean {
  if (e.tag === 'rational') return rationalIsZero(e.value)
  if (e.tag === 'surd') return surdIsRational(e.value) && rationalIsZero(e.value.a)
  return e.value === 0
}

/** Check if ExactNumber is rational */
export function exactIsRational(e: ExactNumber): e is { tag: 'rational', value: Rational } {
  return e.tag === 'rational'
}

/** Check if ExactNumber is a surd */
export function exactIsSurd(e: ExactNumber): e is { tag: 'surd', value: QuadraticSurd } {
  return e.tag === 'surd'
}

/** Convert ExactNumber to surd form (rationals become surds with b=0) */
function exactToSurd(e: ExactNumber): QuadraticSurd | undefined {
  if (e.tag === 'rational') return surdFromRational(e.value)
  if (e.tag === 'surd') return e.value
  return undefined // float cannot be converted to surd
}

/** Add two ExactNumbers - stays exact if possible */
export function exactAdd(a: ExactNumber, b: ExactNumber): ExactNumber {
  // Try to stay in surd form if possible
  const aS = exactToSurd(a)
  const bS = exactToSurd(b)
  if (aS && bS) {
    const result = surdAdd(aS, bS)
    if (result) return exactFromSurd(result)
  }
  // Fall back to float
  return { tag: 'float', value: exactToFloat(a) + exactToFloat(b) }
}

/** Divide two ExactNumbers - stays exact if possible */
export function exactDiv(a: ExactNumber, b: ExactNumber): ExactNumber {
  if (exactIsZero(b)) throw new Error('ExactNumber: division by zero')
  // Try to stay in surd form
  const aS = exactToSurd(a)
  const bS = exactToSurd(b)
  if (aS && bS) {
    const result = surdDiv(aS, bS)
    if (result) return exactFromSurd(result)
  }
  // Fall back to float
  return { tag: 'float', value: exactToFloat(a) / exactToFloat(b) }
}

/** Subtract two ExactNumbers - stays exact if possible */
export function exactSub(a: ExactNumber, b: ExactNumber): ExactNumber {
  const aS = exactToSurd(a)
  const bS = exactToSurd(b)
  if (aS && bS) {
    const result = surdSub(aS, bS)
    if (result) return exactFromSurd(result)
  }
  return { tag: 'float', value: exactToFloat(a) - exactToFloat(b) }
}

/** Multiply two ExactNumbers - stays exact if possible */
export function exactMul(a: ExactNumber, b: ExactNumber): ExactNumber {
  const aS = exactToSurd(a)
  const bS = exactToSurd(b)
  if (aS && bS) {
    const result = surdMul(aS, bS)
    if (result) return exactFromSurd(result)
  }
  return { tag: 'float', value: exactToFloat(a) * exactToFloat(b) }
}

/** Negate an ExactNumber */
export function exactNeg(a: ExactNumber): ExactNumber {
  if (a.tag === 'rational') {
    return { tag: 'rational', value: { numer: -a.value.numer, denom: a.value.denom } }
  }
  if (a.tag === 'surd') {
    return { tag: 'surd', value: surdNeg(a.value) }
  }
  return { tag: 'float', value: -a.value }
}

/** Power - falls back to float since rational^rational is often irrational */
export function exactPow(base: ExactNumber, exp: ExactNumber): ExactNumber {
  // For now, always use float for power operations (could handle integer exponents specially)
  return { tag: 'float', value: Math.pow(exactToFloat(base), exactToFloat(exp)) }
}

/** Format ExactNumber for display - fraction if rational, surd if algebraic, decimal if float */
export function exactToString(e: ExactNumber): string {
  if (e.tag === 'rational') {
    return rationalToString(e.value)
  }
  if (e.tag === 'surd') {
    return surdToString(e.value)
  }
  // For floats, show reasonable precision
  const v = e.value
  if (Number.isInteger(v)) return v.toString()
  // Show up to 4 decimal places, trimming trailing zeros
  return v.toFixed(4).replace(/\.?0+$/, '')
}

/**
 * Try to parse a Z3 root-obj expression as an exact surd.
 * Z3's root-obj format for quadratics: (root-obj (+ (* a (^ x 2)) (* b x) c) index)
 * Represents roots of ax² + bx + c = 0.
 * Index 1 = (-b - √Δ)/(2a), Index 2 = (-b + √Δ)/(2a) where Δ = b² - 4ac.
 * Returns undefined if not a parseable quadratic root-obj.
 */
function parseRootObjAsSurd(sexpr: string): ExactNumber | undefined {
  // Parse the S-expression
  let parsed: S
  try {
    parsed = parse_s(sexpr)
  } catch {
    return undefined
  }

  if (!Array.isArray(parsed) || parsed[0] !== 'root-obj') {
    return undefined
  }

  // Extract the polynomial and index
  const poly = parsed[1]
  const indexS = parsed[2]
  if (!Array.isArray(poly) || poly[0] !== '+') {
    return undefined
  }

  const index = typeof indexS === 'string' ? parseInt(indexS) : typeof indexS === 'number' ? indexS : NaN
  if (isNaN(index) || (index !== 1 && index !== 2)) {
    return undefined // Only handle roots 1 and 2 (quadratic)
  }

  // Try to extract coefficients a, b, c from ax² + bx + c
  // The format is (+ (* a (^ x 2)) (* b x) c) or variations
  let a = 0, b = 0, c = 0

  for (let i = 1; i < poly.length; i++) {
    const term = poly[i]
    if (typeof term === 'string' || typeof term === 'number') {
      // Constant term
      c += parseCoefficient(term)
    } else if (Array.isArray(term)) {
      if (term[0] === '-' && term.length === 2) {
        // Negation like (- 1)
        c -= parseCoefficient(term[1])
      } else if (term[0] === '*') {
        // Coefficient times x or x²
        const hasX2 = JSON.stringify(term).includes('"^","x","2"') || JSON.stringify(term).includes('^","x",2')
        const hasX = JSON.stringify(term).includes('"x"') || JSON.stringify(term).includes("'x'")

        if (hasX2) {
          a += parseCoefficient(term[1])
        } else if (hasX) {
          b += parseCoefficient(term[1])
        }
      }
    }
  }

  // Need non-zero a for quadratic
  if (a === 0) return undefined

  // Compute discriminant Δ = b² - 4ac
  const discriminant = b * b - 4 * a * c

  // Discriminant must be non-negative for real roots
  if (discriminant < 0) return undefined

  // If discriminant is 0, root is rational: -b/(2a)
  if (discriminant === 0) {
    return exactFromRational(rational(BigInt(-b), BigInt(2 * a)))
  }

  // Root is (-b ± √Δ)/(2a)
  // As a surd: -b/(2a) + (±1/(2a))√Δ
  const negB = BigInt(-b)
  const twoA = BigInt(2 * a)

  // Simplify the surd √Δ to extract perfect square factors
  const [sqFactor, sqFreeDisc] = extractSquareFactor(BigInt(discriminant))

  // The coefficient of √(sqFreeDisc) is ±sqFactor/(2a)
  const sign = index === 2 ? 1n : -1n
  const surdCoef = rational(sign * sqFactor, twoA)
  const rationalPart = rational(negB, twoA)

  return exactFromSurd(surd(rationalPart, surdCoef, sqFreeDisc))
}

/** Helper to parse a coefficient from an S-expression term */
function parseCoefficient(term: S): number {
  if (typeof term === 'number') return term
  if (typeof term === 'string') {
    const n = parseFloat(term)
    return isNaN(n) ? 0 : n
  }
  if (Array.isArray(term)) {
    if (term[0] === '-' && term.length === 2) {
      return -parseCoefficient(term[1])
    }
    if (term[0] === '/') {
      return parseCoefficient(term[1]) / parseCoefficient(term[2])
    }
  }
  return 0
}

/**
 * Extract all variable values from a Z3 model as ExactNumbers.
 * Returns rationals when Z3 gives exact rational values, surds for algebraic, floats otherwise.
 * This handles any variable format (a_1, a_1_1, _p0, etc.)
 */
export const model_to_named_assignments_exact = async <CtxKey extends string>(
  ctx: Context<CtxKey>,
  model: Model<CtxKey>
): Promise<Record<string, ExactNumber>> => {
  const assignments: Record<string, ExactNumber> = {}

  for (const decl of model.decls()) {
    if (decl.arity() !== 0) {
      continue
    }
    const name = decl.name().toString()
    const expr = await ctx.simplify(model.eval(decl.call()))
    const sexpr = expr.sexpr()

    // Try to parse rational like (/ 24 31) or (/ 1.0 4.0)
    // Z3 sometimes returns decimals like 1.0 instead of 1
    const ratMatch = sexpr.match(/^\(\/ (-?\d+(?:\.\d+)?)\s+(-?\d+(?:\.\d+)?)\)$/)
    if (ratMatch) {
      // Parse as floats first, then convert to bigint (handles 1.0 -> 1)
      const numer = BigInt(Math.round(parseFloat(ratMatch[1])))
      const denom = BigInt(Math.round(parseFloat(ratMatch[2])))
      assignments[name] = exactFromRational(rational(numer, denom))
      continue
    }

    // Try to parse as integer
    const intMatch = sexpr.match(/^(-?\d+)$/)
    if (intMatch) {
      assignments[name] = exactFromRational(rationalFromInt(BigInt(intMatch[1])))
      continue
    }

    // Try to parse as simple decimal like 0.0 or 1.0 (Z3's integer representation)
    const simpleFloatMatch = sexpr.match(/^(-?\d+\.\d+)$/)
    if (simpleFloatMatch) {
      const floatVal = parseFloat(simpleFloatMatch[1])
      // Check if it's actually an integer (like 1.0)
      if (Number.isInteger(floatVal)) {
        assignments[name] = exactFromRational(rationalFromInt(BigInt(floatVal)))
        continue
      }
      // Convert to rational
      const str = floatVal.toString()
      const decimalIndex = str.indexOf('.')
      if (decimalIndex !== -1) {
        const decimals = str.length - decimalIndex - 1
        const denom = BigInt(10 ** decimals)
        const numer = BigInt(Math.round(floatVal * Number(denom)))
        assignments[name] = exactFromRational(rational(numer, denom))
        continue
      }
    }

    // Try to parse root-obj as exact surd
    const surdResult = parseRootObjAsSurd(sexpr)
    if (surdResult) {
      console.log(`Z3 returned root-obj for ${name}: ${sexpr} -> ${exactToString(surdResult)}`)
      assignments[name] = surdResult
      continue
    }

    // For anything else, fall back to float
    // Try to evaluate numerically using the S-expression parser
    const floatVal = parseFloat(sexpr)
    if (!isNaN(floatVal)) {
      assignments[name] = exactFromFloat(floatVal)
    } else {
      // Use parse_and_evaluate which handles root-obj (algebraic numbers)
      try {
        const parsed_s = parse_s(sexpr)
        const evaluatedVal = parse_and_evaluate(parsed_s)
        console.log(`Z3 returned algebraic expression for ${name}: ${sexpr} -> ${evaluatedVal}`)
        assignments[name] = exactFromFloat(evaluatedVal)
      } catch (e) {
        console.log(`Z3 returned non-parseable expression for ${name}: ${sexpr}, defaulting to 0`)
        assignments[name] = exactFromFloat(0)  // Default to 0 if we can't parse
      }
    }
  }

  return assignments
}

/**
 * Extract all variable values from a Z3 model, keyed by variable name.
 * This handles any variable format (a_1, a_1_1, _p0, etc.)
 */
export const model_to_named_assignments = async <CtxKey extends string>(
  ctx: Context<CtxKey>,
  model: Model<CtxKey>
): Promise<Record<string, number>> => {
  const assignments: Record<string, number> = {}

  for (const decl of model.decls()) {
    if (decl.arity() !== 0) {
      continue
    }
    const name = decl.name().toString()
    const expr = await ctx.simplify(model.eval(decl.call()))
    const sexpr = expr.sexpr()

    // Try to parse the value as a number
    const value = parseFloat(sexpr)
    if (!isNaN(value)) {
      assignments[name] = value
    } else {
      // Handle rational numbers like (/ 1 2) or more complex expressions
      const ratMatch = sexpr.match(/^\(\/ (-?\d+(?:\.\d+)?)\s+(-?\d+(?:\.\d+)?)\)$/)
      if (ratMatch) {
        assignments[name] = parseFloat(ratMatch[1]) / parseFloat(ratMatch[2])
      } else {
        // For other complex expressions, try to extract a simple value
        const simpleMatch = sexpr.match(/^(-?\d+(?:\.\d+)?)$/)
        if (simpleMatch) {
          assignments[name] = parseFloat(simpleMatch[1])
        }
        // Skip values we can't parse
      }
    }
  }

  return assignments
}

export const model_to_assignments = async <CtxKey extends string>(ctx: Context<CtxKey>, model: Model<CtxKey>): Promise<Record<number, ModelAssignmentOutput>> => {
  const assignments_map: Record<number, ModelAssignmentOutput> = {}
  const assigned_exprs = await model_to_assigned_exprs(ctx, model)
  for (const [index, expr] of assigned_exprs) {
    assignments_map[index] = await expr_to_assignment(ctx, model, expr)
  }
  return assignments_map
}

const constraint_or_real_expr_to_z3_expr = <CtxKey extends string>(ctx: Context<CtxKey>, model: Model<CtxKey>, c_or_re: ConstraintOrRealExpr): Expr<CtxKey> => {
  if (c_or_re.tag === 'constraint') {
    return constraint_to_bool(ctx, model, c_or_re.constraint)
  } else if (c_or_re.tag === 'real_expr') {
    return real_expr_to_arith(ctx, model, c_or_re.real_expr)
  } else {
    return fallthrough('constraint_or_real_expr_to_z3_expr', c_or_re)
  }
}

export const real_expr_to_arith = <CtxKey extends string>(ctx: Context<CtxKey>, model: Model<CtxKey>, expr: RealExpr): Arith<CtxKey> => {
  const sub = (expr: RealExpr): Arith<CtxKey> => real_expr_to_arith(ctx, model, expr)
  if (expr.tag === 'divide') {
    return ctx.Div(sub(expr.numerator), sub(expr.denominator))
  } else if (expr.tag === 'given_probability') {
    throw new Error('Unable to convert conditional probability to a Z3 arith expression!')
  } else if (expr.tag === 'literal') {
    return ctx.Real.val(expr.value)
  } else if (expr.tag === 'minus') {
    return ctx.Sub(sub(expr.left), sub(expr.right))
  } else if (expr.tag === 'multiply') {
    return ctx.Product(sub(expr.left), sub(expr.right))
  } else if (expr.tag === 'negative') {
    return ctx.Neg(sub(expr.expr))
  } else if (expr.tag === 'plus') {
    return ctx.Sum(sub(expr.left), sub(expr.right))
  } else if (expr.tag === 'power') {
    throw new Error('Unable to convert exponent to Z3 arith expression (be careful where real_expr_to_arith is called!)')
  } else if (expr.tag === 'state_variable_sum') {
    if (expr.indices.length === 0) {
      return ctx.Real.val(0)
    } else {
      const first_var_expr = ctx.Const(state_index_id(expr.indices[0]), ctx.Real.sort())
      const rest_var_exprs = expr.indices.slice(1).map((state_index) => ctx.Const(state_index_id(state_index), ctx.Real.sort()))
      return ctx.Sum(first_var_expr, ...rest_var_exprs)
    }
  } else if (expr.tag === 'variable') {
    throw new Error('Unable to convert variable to Z3 arith expression (be careful where real_expr_to_arith is called!)')
  } else {
    return fallthrough('real_expr_to_arith', expr)
  }
}

export const constraint_to_bool = <CtxKey extends string>(ctx: Context<CtxKey>, model: Model<CtxKey>, c: Constraint): Bool<CtxKey> => {
  const sub = (c: Constraint): Bool<CtxKey> => constraint_to_bool(ctx, model, c)
  const sub_real = (e: RealExpr): Arith<CtxKey> => real_expr_to_arith(ctx, model, e)
  if (c.tag === 'biconditional') {
    return ctx.Iff(sub(c.left), sub(c.right))
  } else if (c.tag === 'conditional') {
    return ctx.Implies(sub(c.left), sub(c.right))
  } else if (c.tag === 'conjunction') {
    return ctx.And(sub(c.left), sub(c.right))
  } else if (c.tag === 'disjunction') {
    return ctx.Or(sub(c.left), sub(c.right))
  } else if (c.tag === 'equal') {
    return ctx.Eq(sub_real(c.left), sub_real(c.right))
  } else if (c.tag === 'greater_than') {
    return ctx.GT(sub_real(c.left), sub_real(c.right))
  } else if (c.tag === 'greater_than_or_equal') {
    return ctx.GE(sub_real(c.left), sub_real(c.right))
  } else if (c.tag === 'less_than') {
    return ctx.LT(sub_real(c.left), sub_real(c.right))
  } else if (c.tag === 'less_than_or_equal') {
    return ctx.LE(sub_real(c.left), sub_real(c.right))
  } else if (c.tag === 'negation') {
    return ctx.Not(sub(c.constraint))
  } else if (c.tag === 'not_equal') {
    return ctx.Not(ctx.Eq(sub_real(c.left), sub_real(c.right)))
  } else {
    return fallthrough('constraint_to_bool', c)
  }
}

export type SolverOptions = {
  regular: boolean
  timeout_ms: number
}

export type SolverReturn<CtxKey extends string> =
  | {
    status: 'sat'
    all_constraints: Constraint[]
    tt: TruthTable
    z3_model: Model<CtxKey>
    model: Record<number, ModelAssignmentOutput>
    // solver: Solver<CtxKey>
  }
  | { status: 'unsat' | 'unknown', all_constraints: Constraint[], tt: TruthTable, model: undefined }

const DEFAULT_SOLVER_OPTIONS: SolverOptions = {
  regular: false,
  timeout_ms: 30_000,
}

// const fill_solver_options = (defaults: SolverOptions, partial: Partial<SolverOptions> | undefined): SolverOptions =>
//   ({ ...defaults, ...partial })

export const pr_sat_with_options = async <CtxKey extends string>(
  ctx: Context<CtxKey>,
  tt: TruthTable,
  constraints: Constraint[],
  options?: Partial<SolverOptions>,
): Promise<SolverReturn<CtxKey>> => {
  const { regular, timeout_ms } = { ...DEFAULT_SOLVER_OPTIONS, ...options }
  const { Solver } = ctx
  const solver = new Solver('QF_NRA');
  solver.set("timeout", timeout_ms)

  const translated = translate(tt, constraints)
  const index_to_eliminate = tt.n_states() - 1  // Only this works right now!
  // const index_to_eliminate = 0
  const enriched_constraints = enrich_constraints(tt, index_to_eliminate, regular, translated)
  const [redef, elim_constraints] = eliminate_state_variable_index(tt.n_states(), index_to_eliminate, enriched_constraints)

  const smtlib_lines = [
    ...constraints_to_smtlib_lines(tt, index_to_eliminate, elim_constraints),
    ['define-fun', `s_${index_to_eliminate}`, [], 'Real', real_expr_to_smtlib(redef)],
  ]
  const smtlib_string = smtlib_lines.map((l) => s_to_string(l, false)).join('\n')
  console.log(smtlib_string)
  solver.fromString(smtlib_string)
  const result = await solver.check()

  if (result === 'sat') {
    const model = solver.model()

    const elim_var_value = await fancy_evaluate_constraint_or_real_expr(ctx, model, tt, { tag: 'real_expr', real_expr: redef })
    if (elim_var_value.tag !== 'result') {
      throw new Error('Oh no error when trying to calculate eliminated variable!')
    }

    const assignments = {
      ...await model_to_assignments(ctx, model),
      [index_to_eliminate]: elim_var_value.result,
    }
    return { status: 'sat', all_constraints: translated, tt, z3_model: model, model: assignments }
  } else {
    return { status: result, all_constraints: translated, tt, model: undefined }
  }
}

export const pr_sat_with_truth_table = async <CtxKey extends string>(
  ctx: Context<CtxKey>,
  tt: TruthTable,
  constraints: Constraint[],
  regular: boolean = false,
): Promise<SolverReturn<CtxKey>> => {
  return await pr_sat_with_options(ctx, tt, constraints, { regular })
}

export const pr_sat = async <CtxKey extends string>(
  ctx: Context<CtxKey>,
  constraints: Constraint[],
  regular: boolean = false,
): Promise<SolverReturn<CtxKey>> => {
  const tt = new TruthTable(variables_in_constraints(constraints))
  return pr_sat_with_truth_table(ctx, tt, constraints, regular)
}

// const ac = new AbortController()
// const as = ac.signal
// as.onabort = () => {
// }

export type WrappedSolverResult =
  | {
    status: 'sat'
    state_assignments: Record<number, ModelAssignmentOutput>
    named_assignments: Record<string, number>  // All variable values keyed by name (floats - for backward compat)
    named_assignments_exact: Record<string, ExactNumber>  // All variable values as exact numbers (rational or float)
    evaluate(tt: TruthTable, c_or_re: ConstraintOrRealExpr): Promise<FancyEvaluatorOutput>
  }
  | { status: 'unsat' }
  | { status: 'unknown' }
  | { status: 'exception', message: string }
  | { status: 'cancelled' }

type SolverOptions2 = {
  regular: boolean
  abort_signal?: AbortSignal
  cancel_fallback?: () => Promise<undefined>
  onTranslated?: (translated: Constraint[]) => void
}

const DEFAULT_SOLVER_OPTIONS2: SolverOptions2 = {
  regular: false,
  abort_signal: undefined,
}

export type PrSATResult = {
  constraints: {
    original: Constraint[]
    translated: Constraint[]
    extra: Constraint[]
    eliminated: Constraint[]
  }
  smtlib_input: string,
  solver_output: WrappedSolverResult
}

export const pr_sat_wrapped = async (
  solver: WrappedSolver,
  tt: TruthTable,
  constraints: Constraint[],
  options?: Partial<SolverOptions2>,
): Promise<PrSATResult> => {
  const { regular, abort_signal, cancel_fallback, onTranslated } = { ...DEFAULT_SOLVER_OPTIONS2, ...(options ?? {}) }

  const translated = translate(tt, constraints)
  onTranslated?.(translated)
  const index_to_eliminate = tt.n_states() - 1  // Only this works right now!
  const enriched_constraints = enrich_constraints(tt, index_to_eliminate, regular, translated)
  const [redef, elim_constraints] = eliminate_state_variable_index(tt.n_states(), index_to_eliminate, enriched_constraints)

  const smtlib_lines = constraints_to_smtlib_lines(tt, index_to_eliminate, elim_constraints)
  const smtlib_string = smtlib_lines.map((s) => s_to_string(s, false)).join('\n')
  // const result = await solver.solve(smtlib_lines, abort_signal, cancel_fallback)
  const result = await solver.solve(smtlib_string, abort_signal, cancel_fallback)
  const output_constraints = {
    original: constraints,
    translated,
    extra: enriched_constraints,
    eliminated: elim_constraints,
  }

  if (result.status === 'sat') {
    const elim_var_value = await result.evaluate(tt, { tag: 'real_expr', real_expr: redef })
    if (elim_var_value.tag !== 'result') {
      throw new Error('Oh no error when trying to calculate eliminated variable!')
    }

    return {
      constraints: output_constraints,
      smtlib_input: smtlib_string + `\n(check-sat)\n(get-model)`,
      solver_output: {
        ...result,
        state_assignments: { ...result.state_assignments, [index_to_eliminate]: elim_var_value.result },
      }
    }
  } else {
    return {
      constraints: output_constraints,
      smtlib_input: smtlib_string + `\n(check-sat)`,
      solver_output: result,
    }
  }
}

// I should probably be running z3 inside of a worker.
// Then I could just kill it if it's taking too long to cancel normally.
// Whatever I'll just be weird and do this instead.

export const run_solve_cancel_logic = async <R>(
  on_run: (signal?: AbortSignal) => Promise<R>,
  on_cancel: () => Promise<R>,
  on_slow_cancel: () => Promise<R>,
  cancel_timeout_ms: number,  // amount of time into running on_cancel that we go ahead and call on_slow_cancel.
  abort_signal?: AbortSignal,
): Promise<R> => {
  // This function is about to get more complicated -- yay!
  // On cancel, attempt interrupt.
  // If the interrupt succeeds within a certain timeout, resolve with a 'cancel' status.
  // If the interrupt does NOT succeed within the timeout, resolve anyway with a 'cancel' status.
  // Otherwise everything else should resolve normally.

  // The ways the Promise can resolve:
  // - on_run finishes.
  // - abort_signal.abort event and on_cancel finishes before given cancel timeout.
  // - abort_signal.abort event and on_cancel finishes after given cancel timeout (on_slow_cancel).

  const user_cancel = new Promise<{ tag: 'cancelled' }>((resolve) => {
    abort_signal?.addEventListener('abort', () => {
      resolve({ tag: 'cancelled' })
    })
  })

  const run = on_run(abort_signal).then((r) => ({ tag: 'finished' as const, result: r }))
  const result = await Promise.race([
    run,
    user_cancel,
  ])

  if (result.tag === 'finished') {
    return result.result
  } else if (result.tag === 'cancelled') {
    const cancel_result = await on_cancel()
    const result = await Promise.race([
      // If we're at this point, just assume that the run finishes BECAUSE it was cancelled.
      // Ignore the result, though, as it's (best-case) garbage.
      run.then(() => ({ tag: 'finished' as const, result: cancel_result })),
      // on_cancel().then((r) => ({ tag: 'finished' as const, result: r })),
      sleep(cancel_timeout_ms).then(() => ({ tag: 'cancelled' as const })),
    ])

    if (result.tag === 'finished') {
      return result.result
    } else if (result.tag === 'cancelled') {
      return await on_slow_cancel()
    } else {
      return fallthrough('run_solve_cancel_logic', result)
    }
  } else {
    return fallthrough('run_solve_cancel_logic', result)
  }
}

export class WrappedSolver {
  constructor(private z3_interface: (Z3HighLevel & Z3LowLevel) | undefined, private readonly init: () => Promise<(Z3HighLevel & Z3LowLevel) | undefined>) {
  }

  private async reinitialize(): Promise<void> {
    const old = this.z3_interface

    this.z3_interface = await this.init()
    console.log('reinitialized?', old !== this.z3_interface)
  }

  // async solve(smtlib_lines: S[], abort_signal?: AbortSignal, cancel_fallback?: () => Promise<undefined>): Promise<WrappedSolverResult> {
  async solve(smtlib_string: string, abort_signal?: AbortSignal, cancel_fallback?: () => Promise<undefined>): Promise<WrappedSolverResult> {
    // This function is about to get more complicated -- yay!
    // On cancel, attempt interrupt.
    // If the interrupt succeeds within a certain timeout, resolve with a 'cancel' status.
    // If the interrupt does NOT succeed within the timeout, resolve anyway with a 'cancel' status.
    // Otherwise everything else should resolve normally.
    // This logic is complex enough it might be a good idea to make this mockable.

    // const used_ctx = this.z3_interface.Context('main')
    // const solver = new used_ctx.Solver('QF_NRA')
    // const smtlib_lines_string = smtlib_lines.map((s) => s_to_string(s, false)).join('\n')

    return await run_solve_cancel_logic<WrappedSolverResult>(
      async (abort_signal?: AbortSignal): Promise<WrappedSolverResult> => {  // on_run
        if (this.z3_interface === undefined) {
          return { status: 'cancelled' }
        }

        const used_ctx = this.z3_interface.Context('main')
        const solver = new used_ctx.Solver('QF_NRA')
        // const smtlib_lines_string = smtlib_lines.map((s) => s_to_string(s, false)).join('\n')
        const smtlib_lines_string = smtlib_string

        try {
          solver.fromString(smtlib_lines_string)
        } catch (e: any) {
          console.error('smtlib_lines:\n', smtlib_lines_string)
          throw e
        }

        // let interrupted = false
        const on_abort = () => {
          // interrupted = true
          used_ctx.interrupt()
        }
        abort_signal?.addEventListener('abort', on_abort)

        try {
          const result = await solver.check()
          if (result === 'sat') {
            const model = solver.model()
            const evaluate = async (tt: TruthTable, c_or_re: ConstraintOrRealExpr): Promise<FancyEvaluatorOutput> => {
              return await fancy_evaluate_constraint_or_real_expr(used_ctx, model, tt, c_or_re)
            }
            const state_assignments = await model_to_assignments(used_ctx, model)
            const named_assignments = await model_to_named_assignments(used_ctx, model)
            const named_assignments_exact = await model_to_named_assignments_exact(used_ctx, model)
            return { status: 'sat', evaluate, state_assignments, named_assignments, named_assignments_exact }
          } else {
            return { status: result }
          }
        } catch (e: any) {
          return { status: 'exception', message: e.message }
        } finally {
          abort_signal?.removeEventListener('abort', on_abort)
        }

      },
      async () => {  // on_cancel
        // Reinitialize Z3 after any cancel - the context may be in a bad state after interrupt
        await this.reinitialize()
        return { status: 'cancelled' }
      },
      async () => {  // on_slow_cancel
        console.log('attempting slow cancel...')
        await cancel_fallback?.()
        await this.reinitialize()
        return { status: 'cancelled' }
      },
      2 * 2000,  // two seconds before slow_cancel
      abort_signal,
    )
  }
}

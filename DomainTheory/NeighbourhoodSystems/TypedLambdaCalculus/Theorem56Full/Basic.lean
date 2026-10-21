/-ai
This file gathers and re-exports the definitions for the full form of Scott's Theorem 5.6, that every partial recursive function is λ-definable by a very strict approximable map from the universal argument domain into the flat naturals: the λ-definability predicate, the strictifier guards, the tuple map, the primitive-recursion and minimization combinators, evaluation at a stack, and the component computations for argument and vector elements.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import Mathlib.Computability.PartrecBasis
import all Mathlib.Computability.PartrecBasis
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.LamDef
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.guard1
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.strictGuardN
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.tupleMap
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.precBody
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.recOp
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.recMap
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.findBody
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.findOp
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.searchMap
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.findMap
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.evalAt
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.rfindZeroPred
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.oneArg
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.component_argElem
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.component_vecElem

@[expose] public section

/-!
# Theorem 5.6 (Scott 1981, PRG-19, §5) — the FULL closure: partial recursive ⟹ λ-definable

`Theorem56.lean` builds the constructive heart (strict starting functions, the primitive-recursion
and μ combinators with their scheme equations). This file wires those pieces together against
Mathlib's **arity-aware** inductive predicates `Nat.Primrec'`/`Nat.Partrec'` (over `List.Vector ℕ n`),
whose constructors are *exactly* Scott's generation grammar:

* `Nat.Primrec'`: `zero`, `succ`, `get i` (projection), `comp`, `prec` (primitive recursion);
* `Nat.Partrec'`: `prim`, `comp`, `rfind` (minimization).

We prove: every `Nat.Primrec'`/`Nat.Partrec'` function is denoted by an approximable map
`φ : 𝒩 → N`, where `𝒩 := N^∞` (Exercise 3.16) is the **universal argument domain** — a `k`-ary
function is realised by a single map that depends only on coordinates `0..k-1`. The realisation is
*very strict* (Scott): `⊥` in any relevant coordinate forces `⊥`, which is what makes composition and
minimisation compose. The capstone is `partrec_lamDef` and the 1-ary corollary `partrec_one`.
-/

namespace DomainTheory.NeighbourhoodSystems.Theorem56Full

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)
open DomainTheory.NeighbourhoodSystems.Exercise511 (head tail push)

/-! ### Element builders. -/





/-! ### Components through `push`. -/

/-! ### The strictifier `guard1`/`strictGuardN` (Scott's `cond(zero(x),·,·)` device).

`guard1 j φ z = cond(zero(zⱼ), φ z, φ z)`: equals `φ z` when `zⱼ` is total, `⊥` when `zⱼ = ⊥`.
Composing the guards for `j = 0..n-1` makes a map *very strict* in its first `n` coordinates. -/



/-! ### `tupleMap`: assemble `n` scalar maps into the first `n` coordinates of `𝒩`. -/


/-! ### The λ-definability specification. -/


/-! ### Primitive recursive base cases: `zero`, `succ`, `get`. -/

/-! ### Composition. -/

/-! ### `vecElem` of a cons is a `push`. -/

/-! ### Primitive recursion.

The recursion lives over `prod (funSpace 𝒩 N) 𝒩`: `k` is the unknown, `z` the argument stack whose
head is the recursion variable and whose tail carries the parameters. The body is
`M(k, z) = cond(zero(head z), f(tail z), g(⟨pred(head z), ⟨k(⟨pred(head z), tail z⟩), tail z⟩⟩))`. -/

section Prec

variable (φf φg : ApproximableMap 𝒩 N)




end Prec

/-! ### Closure of the primitive recursive functions. -/

/-! ### Minimisation (`rfind`).

The μ-operator searches *upward* for the least `k` with `f(k ::ᵥ v) = 0`. We carry the counter in the
head coordinate of the stack. The search body over `prod (funSpace 𝒩 N) 𝒩` is

  `S(k, z) = cond(zero(f z), head z, k(push(succ(head z), tail z)))` :

if the current value `f z` is `0`, return the counter `head z`; otherwise recurse with the counter
bumped by one. `searchMap` is the least fixed point, and `findMap` kicks the search off at counter `0`.
The hard direction is **divergence**: when no `k` zeroes `f`, every finite approximant `Sⁿ(⊥)` returns
`⊥` along the search trace, so the directed sup (Theorem 4.2(iii)) is `⊥` too. -/

section Rfind

variable (φf : ApproximableMap 𝒩 N)





/-! #### Divergence via the directed sup of approximants. -/



end Rfind

/-! ### Closure of the partial recursive functions — the full meta-theorem. -/

/-! ### Scott's 1-ary statement.

Every partial recursive `h : ℕ →. ℕ` is realised by an approximable map `τ : N → N` over the flat
naturals: `τ(n̂) = m̂` when `h n = m`, `τ(n̂) = ⊥` when `h n` diverges, and `τ(⊥) = ⊥` (strictness). -/

end DomainTheory.NeighbourhoodSystems.Theorem56Full

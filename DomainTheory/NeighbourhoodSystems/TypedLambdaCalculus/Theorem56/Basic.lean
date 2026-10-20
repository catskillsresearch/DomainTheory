module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.strictId
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.strictProj₀
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.qSel
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.kSel
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.argX
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.argY
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.primBody
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.primOp
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.primRec
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.muBody
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.muOp
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.muRec
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.muMap

@[expose] public section

/-!
# Theorem 5.6 (Scott 1981, PRG-19, §5) — recursive functions are λ-definable

Scott's Theorem 5.6: every partial recursive `h : N → N` is denoted by a λ-term whose only constants
are `cond`, `succ`, `pred`, `zero`, `0`. The proof is by the standard generation of the partial
recursive functions: strict *starting* functions, closure under (multivariate) *composition*,
*primitive recursion*, and the *μ-scheme* (least-number operator). We formalise the constructive
heart of the proof — the actual combinators Scott writes down — over the natural-number domain `N`
(Example 4.3) and the conditional `cond` (Exercise 3.26), proving the defining equations of each
scheme. (We do not also wire these together against an external inductive predicate of partial
recursive functions; that closure is a routine but lengthy induction over the generation grammar,
built entirely from the pieces below.)

## What is proved

* **Strict starting functions** (Scott's "simple device" `λx. cond(zero(x), x, x)`):
  - `strictId` with `strictId_natElem` (`= n̂`) and `strictId_bot` (`= ⊥`);
  - `strictProj₀ : N × N → N`, the strict first projection, with `strictProj₀_natElem`,
    `strictProj₀_bot_left`, `strictProj₀_bot_right` (strict in *both* arguments).

* **Primitive recursion** `primRec f g`, the least fixed point
  `!k λx,y. cond(zero(x), f(y), g(pred(x), y, k(pred(x), y)))`, with the scheme equations
  - `primRec_zero` : `h̄(0̂, m̂) = f(m̂)`,
  - `primRec_succ` : `h̄((n+1)^, m̂) = g(n̂, m̂, h̄(n̂, m̂))`,
  - `primRec_bot`  : `h̄(⊥, m̂) = ⊥`  (strict in the recursion argument).

* **The μ-scheme** `muRec f` / `muMap f`, the least fixed point
  `!g λx,y. cond(zero(f(x,y)), x, g(succ(x), y))` and `h̄ = λy. ḡ(0̂, y)`, with
  - `muRec_found` : `f(n̂, m̂) = 0̂  ⟹  ḡ(n̂, m̂) = n̂`,
  - `muRec_step`  : `f(n̂, m̂) = (j+1)^  ⟹  ḡ(n̂, m̂) = ḡ((n+1)^, m̂)`,
  - `muRec_bot`   : `f(n̂, m̂) = ⊥  ⟹  ḡ(n̂, m̂) = ⊥`,
  and the **capstone** `muMap_eq_least`: if `n₀` is the least zero of `f(·, m̂)` (all earlier values
  positive totals), then `μ(m̂) = n̂₀`.

All `cond`-based maps inherit `Classical.choice` structurally from the truth domain `T`
(Example 1.2) exactly as `cond`/`zeroMap` already do; the fixed points come from Theorem 4.1.
-/

namespace DomainTheory.NeighbourhoodSystems.Theorem56

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN constLiftN_natElem)
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)

/-! ### Strict starting functions (`λx. cond(zero x, x, x)`). -/



/-! ### Primitive recursion.

Given `f : N → N` and `g : N × N × N → N` (with `N³` modelled as `N × (N × N)`), the primitive
recursion `h̄` with `h̄(0, m) = f(m)`, `h̄(n+1, m) = g(n, m, h̄(n, m))` is the least fixed point of
`λk λx,y. cond(zero(x), f(y), g(pred(x), y, k(pred(x), y)))`. -/

/-! ### Selector maps on `(N×N → N) × (N×N)`.

The recursion bodies live over `prod F Q` with `F = funSpace (N×N) N` (the unknown) and `Q = N × N`
(the argument pair). We name the four selectors once to keep the body terms readable. -/





section PrimRec

variable (f : ApproximableMap N N) (g : ApproximableMap (prod N (prod N N)) N)




end PrimRec

/-! ### The μ-scheme (least-number operator).

Given `f : N × N → N`, the minimization `h̄(m) = μn. f(n, m) = 0` is obtained from
`ḡ = !g λx,y. cond(zero(f(x,y)), x, g(succ(x), y))` by `h̄ = λy. ḡ(0̂, y)`. -/

section Mu

variable (f : ApproximableMap (prod N N) N)




end Mu
end DomainTheory.NeighbourhoodSystems.Theorem56

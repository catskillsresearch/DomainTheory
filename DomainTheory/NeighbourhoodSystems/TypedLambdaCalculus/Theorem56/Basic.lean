/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Example43
public import DomainTheory.Neighborhood.Exercise326
public import DomainTheory.Neighborhood.FunctionSpace

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

namespace DomainTheory.Neighborhood.Theorem56

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap
open DomainTheory.Neighborhood.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN constLiftN_natElem)
open DomainTheory.Neighborhood.Exercise326 (cond)

/-! ### Strict starting functions (`λx. cond(zero x, x, x)`). -/

/-- Scott's **strict identity** `λx. cond(zero(x), x, x)`: the identity on totals, `⊥` on `⊥`. -/
def strictId : ApproximableMap N N :=
  (cond N).comp (paired zeroMap (paired (idMap N) (idMap N)))

/-- Scott's **strict first projection** `λx₀, x₁. cond(zero(x₁), x₀, x₀)` on `N × N`. -/
def strictProj₀ : ApproximableMap (prod N N) N :=
  (cond N).comp
    (paired (zeroMap.comp (proj₁ N N))
      (paired (proj₀ N N) (proj₀ N N)))

/-! ### Primitive recursion.

Given `f : N → N` and `g : N × N × N → N` (with `N³` modelled as `N × (N × N)`), the primitive
recursion `h̄` with `h̄(0, m) = f(m)`, `h̄(n+1, m) = g(n, m, h̄(n, m))` is the least fixed point of
`λk λx,y. cond(zero(x), f(y), g(pred(x), y, k(pred(x), y)))`. -/

/-! ### Selector maps on `(N×N → N) × (N×N)`.

The recursion bodies live over `prod F Q` with `F = funSpace (N×N) N` (the unknown) and `Q = N × N`
(the argument pair). We name the four selectors once to keep the body terms readable. -/

/-- The argument pair `⟨x, y⟩` (`= proj₁`). -/
def qSel : ApproximableMap (prod (funSpace (prod N N) N) (prod N N)) (prod N N) :=
  proj₁ (funSpace (prod N N) N) (prod N N)

/-- The unknown function `k` (`= proj₀`). -/
def kSel : ApproximableMap (prod (funSpace (prod N N) N) (prod N N)) (funSpace (prod N N) N) :=
  proj₀ (funSpace (prod N N) N) (prod N N)

/-- The first argument `x`. -/
def argX : ApproximableMap (prod (funSpace (prod N N) N) (prod N N)) N := (proj₀ N N).comp qSel

/-- The second argument `y`. -/
def argY : ApproximableMap (prod (funSpace (prod N N) N) (prod N N)) N := (proj₁ N N).comp qSel

section PrimRec

variable (f : ApproximableMap N N) (g : ApproximableMap (prod N (prod N N)) N)

/-- The two-argument body `M(k, ⟨x, y⟩) = cond(zero(x), f(y), g(pred x, y, k(pred x, y)))`. -/
def primBody : ApproximableMap (prod (funSpace (prod N N) N) (prod N N)) N :=
  (cond N).comp
    (paired (zeroMap.comp argX)
      (paired (f.comp argY)
        (g.comp
          (paired (predMap.comp argX)
            (paired argY
              ((evalMap (prod N N) N).comp
                (paired kSel (paired (predMap.comp argX) argY))))))))

/-- The primitive-recursion operator `R(k) = λx,y. cond(zero x, f y, g(pred x, y, k(pred x, y)))`. -/
def primOp : ApproximableMap (funSpace (prod N N) N) (funSpace (prod N N) N) :=
  curry (primBody f g)

/-- `primRec f g : N × N → N`, the least fixed point of `primOp`. -/
def primRec : ApproximableMap (prod N N) N := toApproxMap (primOp f g).fixElement

end PrimRec

/-! ### The μ-scheme (least-number operator).

Given `f : N × N → N`, the minimization `h̄(m) = μn. f(n, m) = 0` is obtained from
`ḡ = !g λx,y. cond(zero(f(x,y)), x, g(succ(x), y))` by `h̄ = λy. ḡ(0̂, y)`. -/

section Mu

variable (f : ApproximableMap (prod N N) N)

/-- The body `M(g, ⟨x, y⟩) = cond(zero(f(x, y)), x, g(succ x, y))`. -/
def muBody : ApproximableMap (prod (funSpace (prod N N) N) (prod N N)) N :=
  (cond N).comp
    (paired (zeroMap.comp (f.comp qSel))
      (paired argX
        ((evalMap (prod N N) N).comp
          (paired kSel (paired (succMap.comp argX) argY)))))

/-- The μ-operator `R(g) = λx,y. cond(zero(f(x, y)), x, g(succ x, y))`. -/
def muOp : ApproximableMap (funSpace (prod N N) N) (funSpace (prod N N) N) :=
  curry (muBody f)

/-- `muRec f : N × N → N`, the binary search `ḡ`, least fixed point of `muOp`. -/
def muRec : ApproximableMap (prod N N) N := toApproxMap (muOp f).fixElement

/-- The minimization `μ : N → N`, `h̄(m) = ḡ(0̂, m)` (the strict `0`-seeded search). -/
def muMap : ApproximableMap N N := muRec f |>.comp (paired (constLiftN N (fun _ => zeroElt)) (idMap N))
end Mu
end DomainTheory.Neighborhood.Theorem56

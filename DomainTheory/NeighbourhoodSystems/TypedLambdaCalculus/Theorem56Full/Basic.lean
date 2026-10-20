/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Example43
public import DomainTheory.Neighborhood.Exercise326
public import DomainTheory.Neighborhood.Exercise511
public import DomainTheory.Neighborhood.Theorem41
public import DomainTheory.Neighborhood.ApproximableExercises
public import Mathlib.Computability.PartrecBasis
import all Mathlib.Computability.PartrecBasis

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

namespace DomainTheory.Neighborhood.Theorem56Full

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap
open DomainTheory.Neighborhood.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)
open DomainTheory.Neighborhood.Exercise326 (cond)
open DomainTheory.Neighborhood.Exercise511 (head tail push)

/-- The universal argument domain `𝒩 = N^∞` (Exercise 3.16). All `k`-ary number functions are
realised as approximable maps `𝒩 → N` depending only on coordinates `0..k-1`. -/
abbrev 𝒩 : NeighborhoodSystem (ℕ × ℕ) := iterSys N

/-! ### Element builders. -/

/-- `none ↦ ⊥`, `some n ↦ n̂`. -/
def optElem : Option ℕ → N.Element
  | none => N.bot
  | some n => natElem n

/-- The argument element of `𝒩` whose first `n` coordinates are `optElem (a i)` and the rest `⊥`. -/
def argElem {n : ℕ} (a : Fin n → Option ℕ) : 𝒩.Element :=
  ofSeq (fun i => if h : i < n then optElem (a ⟨i, h⟩) else N.bot)

/-- The argument element of `𝒩` carrying a `List.Vector ℕ n` in its first `n` coordinates. -/
def vecElem {n : ℕ} (v : List.Vector ℕ n) : 𝒩.Element :=
  argElem (fun i => some (v.get i))

@[simp] theorem component_argElem {n : ℕ} (a : Fin n → Option ℕ) (i : ℕ) :
    component (argElem a) i = if h : i < n then optElem (a ⟨i, h⟩) else N.bot := by
  rw [argElem, component_ofSeq]

@[simp] theorem component_vecElem {n : ℕ} (v : List.Vector ℕ n) (i : ℕ) :
    component (vecElem v) i = if h : i < n then natElem (v.get ⟨i, h⟩) else N.bot := by
  rw [vecElem, component_argElem]; split <;> rfl

/-- A `𝒩`-element is *arg-like* if every coordinate is total or `⊥` (true of all `argElem`). -/
def ArgLike (z : 𝒩.Element) : Prop := ∀ j, component z j = N.bot ∨ ∃ k, component z j = natElem k

/-! ### Components through `push`. -/

/-! ### The strictifier `guard1`/`strictGuardN` (Scott's `cond(zero(x),·,·)` device).

`guard1 j φ z = cond(zero(zⱼ), φ z, φ z)`: equals `φ z` when `zⱼ` is total, `⊥` when `zⱼ = ⊥`.
Composing the guards for `j = 0..n-1` makes a map *very strict* in its first `n` coordinates. -/

/-- Test coordinate `j`: `cond(zero(zⱼ), φ z, φ z)`. -/
def guard1 (j : ℕ) (φ : ApproximableMap 𝒩 N) : ApproximableMap 𝒩 N :=
  (cond N).comp (paired (zeroMap.comp (projN N j)) (paired φ φ))

/-- Test coordinates `0..n-1`. -/
def strictGuardN : ℕ → ApproximableMap 𝒩 N → ApproximableMap 𝒩 N
  | 0, φ => φ
  | n + 1, φ => guard1 n (strictGuardN n φ)

/-! ### `tupleMap`: assemble `n` scalar maps into the first `n` coordinates of `𝒩`. -/

/-- `⟨g₀, …, g_{n-1}⟩ : 𝒩 → 𝒩` placing `gᵢ` at coordinate `i` (`< n`) and `⊥` beyond. -/
def tupleMap : (n : ℕ) → (Fin n → ApproximableMap 𝒩 N) → ApproximableMap 𝒩 𝒩
  | 0, _ => constMap 𝒩 𝒩.bot
  | n + 1, gs => (push N).comp (paired (gs 0) (tupleMap n (fun i => gs i.succ)))

/-! ### The λ-definability specification. -/

/-- `φ : 𝒩 → N` realises the `n`-ary partial function `f` (a *very strict* λ-definition):
`φ` returns `f`'s value on total arguments, `⊥` where `f` is undefined, and `⊥` on *any* arg-like
input with a `⊥` among its first `n` coordinates. -/
structure LamDef {n : ℕ} (φ : ApproximableMap 𝒩 N) (f : List.Vector ℕ n →. ℕ) : Prop where
  defined : ∀ (v : List.Vector ℕ n) (c : ℕ), c ∈ f v → φ.toElementMap (vecElem v) = natElem c
  undef : ∀ (v : List.Vector ℕ n), ¬ (f v).Dom → φ.toElementMap (vecElem v) = N.bot
  strict : ∀ (z : 𝒩.Element), ArgLike z → ∀ i, i < n → component z i = N.bot →
    φ.toElementMap z = N.bot

/-! ### Primitive recursive base cases: `zero`, `succ`, `get`. -/

/-! ### Composition. -/

/-! ### `vecElem` of a cons is a `push`. -/

/-! ### Primitive recursion.

The recursion lives over `prod (funSpace 𝒩 N) 𝒩`: `k` is the unknown, `z` the argument stack whose
head is the recursion variable and whose tail carries the parameters. The body is
`M(k, z) = cond(zero(head z), f(tail z), g(⟨pred(head z), ⟨k(⟨pred(head z), tail z⟩), tail z⟩⟩))`. -/

section Prec

variable (φf φg : ApproximableMap 𝒩 N)

/-- The primitive-recursion body. -/
def precBody : ApproximableMap (prod (funSpace 𝒩 N) 𝒩) N :=
  (cond N).comp
    (paired (zeroMap.comp ((head N).comp (proj₁ (funSpace 𝒩 N) 𝒩)))
      (paired (φf.comp ((tail N).comp (proj₁ (funSpace 𝒩 N) 𝒩)))
        (φg.comp
          ((push N).comp
            (paired (predMap.comp ((head N).comp (proj₁ (funSpace 𝒩 N) 𝒩)))
              ((push N).comp
                (paired
                  ((evalMap 𝒩 N).comp
                    (paired (proj₀ (funSpace 𝒩 N) 𝒩)
                      ((push N).comp
                        (paired (predMap.comp ((head N).comp (proj₁ (funSpace 𝒩 N) 𝒩)))
                          ((tail N).comp (proj₁ (funSpace 𝒩 N) 𝒩))))))
                  ((tail N).comp (proj₁ (funSpace 𝒩 N) 𝒩)))))))))

/-- The primitive-recursion operator `R(k) = λz. …`. -/
def recOp : ApproximableMap (funSpace 𝒩 N) (funSpace 𝒩 N) := curry (precBody φf φg)

/-- `recMap : 𝒩 → N`, the least fixed point of `recOp` (before strictifying). -/
def recMap : ApproximableMap 𝒩 N := toApproxMap (recOp φf φg).fixElement

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

/-- The search body `S(k, z) = cond(zero(f z), head z, k(push(succ(head z), tail z)))`. -/
def findBody : ApproximableMap (prod (funSpace 𝒩 N) 𝒩) N :=
  (cond N).comp
    (paired (zeroMap.comp (φf.comp (proj₁ (funSpace 𝒩 N) 𝒩)))
      (paired ((head N).comp (proj₁ (funSpace 𝒩 N) 𝒩))
        ((evalMap 𝒩 N).comp
          (paired (proj₀ (funSpace 𝒩 N) 𝒩)
            ((push N).comp
              (paired (succMap.comp ((head N).comp (proj₁ (funSpace 𝒩 N) 𝒩)))
                ((tail N).comp (proj₁ (funSpace 𝒩 N) 𝒩))))))))

/-- The search operator `S(k) = λz. …`, whose least fixed point is the running search. -/
def findOp : ApproximableMap (funSpace 𝒩 N) (funSpace 𝒩 N) := curry (findBody φf)

/-- `searchMap : 𝒩 → N`, the least fixed point of `findOp` (the counter lives in coordinate `0`). -/
def searchMap : ApproximableMap 𝒩 N := toApproxMap (findOp φf).fixElement

/-- `findMap : 𝒩 → N` starts the search with counter `0`. -/
def findMap : ApproximableMap 𝒩 N :=
  (searchMap φf).comp ((push N).comp (paired (constMap 𝒩 (natElem 0)) (idMap 𝒩)))

/-! #### Divergence via the directed sup of approximants. -/

/-- `evalAt z` evaluates a function-space element at the fixed argument `z`. -/
def evalAt (z : 𝒩.Element) : ApproximableMap (funSpace 𝒩 N) N :=
  (evalMap 𝒩 N).comp (paired (idMap (funSpace 𝒩 N)) (constMap (funSpace 𝒩 N) z))

/-- The `ℕ →. Bool` predicate `k ↦ f(k ::ᵥ v) = 0`, packaged so `Nat.rfind` is well-typed at
implicit transparency (Lean 4.33: `ℕ →. Bool` no longer unfolds to `ℕ → Part Bool` in `rw`). -/
def rfindZeroPred {n : ℕ} (f : List.Vector ℕ (n + 1) → ℕ) (v : List.Vector ℕ n) : ℕ →. Bool :=
  fun k => Part.some (decide (f (k ::ᵥ v) = 0))

end Rfind

/-! ### Closure of the partial recursive functions — the full meta-theorem. -/

/-! ### Scott's 1-ary statement.

Every partial recursive `h : ℕ →. ℕ` is realised by an approximable map `τ : N → N` over the flat
naturals: `τ(n̂) = m̂` when `h n = m`, `τ(n̂) = ⊥` when `h n` diverges, and `τ(⊥) = ⊥` (strictness). -/

/-- Inject `N → 𝒩` as the stack whose only nonzero coordinate is the head. -/
def oneArg : ApproximableMap N 𝒩 := (push N).comp (paired (idMap N) (constMap N 𝒩.bot))
end DomainTheory.Neighborhood.Theorem56Full

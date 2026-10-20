/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Theorem41
public import DomainTheory.Neighborhood.ApproximableExercises

@[expose] public section

/-!
# Exercise 4.7 (Scott 1981, PRG-19, Lecture IV)

Formula 4.2(iii) gives the *least* fixed point `fix(f) = ⊔ₙ fⁿ(⊥)`. Suppose instead that
`a ∈ |𝒟|` satisfies `a ⊑ f(a)`. *Will there be a fixed point `x = f(x)` with `a ⊑ x`?*

**Yes.** Replace `⊥` by `a`: the chain `a ⊑ f(a) ⊑ f²(a) ⊑ …` is increasing (monotonicity of `f`
applied to `a ⊑ f(a)`), hence *directed*, so its union `x = ⊔ₙ fⁿ(a)` is a genuine element of `|𝒟|`
(Scott's hint: this is why `⊔` makes sense — directed unions of filters are filters, Exercise 2.11 /
`iSupDirected`). Approximable maps preserve directed unions (`toElementMap_iSupDirected`), which makes
`x` a fixed point, and `a = f⁰(a) ⊑ x` by construction. Moreover `x` is the *least* fixed point above
`a` (`fixAbove_least`), the relativized analogue of 4.2(iii).

All constructions are **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- The chain of approximants from a base point `a`: `iterFrom f a n = fⁿ(a)`. -/
def iterFrom (f : ApproximableMap V V) (a : V.Element) (n : ℕ) : V.Element :=
  (f.toElementMap)^[n] a

@[simp] theorem iterFrom_zero (f : ApproximableMap V V) (a : V.Element) :
    f.iterFrom a 0 = a := rfl

theorem iterFrom_succ (f : ApproximableMap V V) (a : V.Element) (n : ℕ) :
    f.iterFrom a (n + 1) = f.toElementMap (f.iterFrom a n) := by
  rw [iterFrom, iterFrom, Function.iterate_succ', Function.comp_apply]

/-- One step of the chain: `fⁿ(a) ⊑ fⁿ⁺¹(a)` (proved choice-free by induction). -/
theorem iterFrom_step (f : ApproximableMap V V) {a : V.Element} (ha : a ≤ f.toElementMap a)
    (n : ℕ) : f.iterFrom a n ≤ f.iterFrom a (n + 1) := by
  induction n with
  | zero => rw [iterFrom_succ f a 0, iterFrom_zero]; exact ha
  | succ k ih =>
    rw [iterFrom_succ f a k, iterFrom_succ f a (k + 1)]
    exact f.toElementMap_mono ih

/-- When `a ⊑ f(a)`, the chain `fⁿ(a)` is monotone: `n ≤ m ⟹ fⁿ(a) ⊑ fᵐ(a)`. Proved by induction
on `n ≤ m` (so as to stay **choice-free**, unlike `monotone_nat_of_le_succ`). -/
theorem iterFrom_mono (f : ApproximableMap V V) {a : V.Element} (ha : a ≤ f.toElementMap a)
    {n m : ℕ} (hnm : n ≤ m) : f.iterFrom a n ≤ f.iterFrom a m := by
  induction hnm with
  | refl => exact le_refl _
  | step _ ih => exact le_trans ih (iterFrom_step f ha _)

/-- The fixed point of `f` lying above a pre-fixed-point candidate `a` (with `a ⊑ f(a)`),
constructed as the directed union `⊔ₙ fⁿ(a)`. -/
def fixAbove (f : ApproximableMap V V) {a : V.Element} (ha : a ≤ f.toElementMap a) : V.Element :=
  NeighborhoodSystem.iSupDirected (f.iterFrom a)
    (fun i j => ⟨max i j, iterFrom_mono f ha (le_max_left i j),
      iterFrom_mono f ha (le_max_right i j)⟩)
end ApproximableMap
end DomainTheory.Neighborhood

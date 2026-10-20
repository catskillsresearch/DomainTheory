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
# Exercise 4.8 (Scott 1981, PRG-19, Lecture IV) — the principle of fixed-point induction

Suppose `f : 𝒟 → 𝒟` and a predicate `S ⊆ |𝒟|` satisfy

  (i)   `⊥ ∈ S`;
  (ii)  `x ∈ S ⟹ f(x) ∈ S`;
  (iii) `S` is closed under sups of increasing sequences.

Then `fix(f) ∈ S`. Since `fix(f) = ⊔ₙ fⁿ(⊥)` (Theorem 4.2(iii)), and `f⁰(⊥) = ⊥ ∈ S` with the
inductive step `fⁿ(⊥) ∈ S ⟹ fⁿ⁺¹(⊥) ∈ S` from (i)/(ii), every approximant lies in `S`; the
directed union then lies in `S` by (iii). This is **fixed-point induction** (`fix_induction`).

As Scott suggests, we apply it to `S = {x ∣ a(x) = b(x)}` (`fix_induction_eq`): if `a, b : 𝒟 → 𝒟`
are approximable with `a(⊥) = b(⊥)`, `f ∘ a = a ∘ f` and `f ∘ b = b ∘ f`, then
`a(fix f) = b(fix f)`. (i) is `a(⊥) = b(⊥)`; (ii) uses the commutation `a(f x) = f(a x)`,
`b(f x) = f(b x)`; (iii) is continuity (`a`, `b` preserve directed unions, `toElementMap_iSupDirected`).

The induction principle is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`); the equality
corollary inherits `Classical.choice` only through the `Element` extensionality used to compare the
two directed unions.
-/

namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- The sup of a monotone `ω`-chain, realized as a directed union (`max`-directedness). -/
def supChain (s : ℕ → V.Element) (hmono : Monotone s) : V.Element :=
  NeighborhoodSystem.iSupDirected s
    (fun i j => ⟨max i j, hmono (le_max_left i j), hmono (le_max_right i j)⟩)
end ApproximableMap
end DomainTheory.Neighborhood

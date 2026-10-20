/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum.sumMap
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum.mem_subset_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum.mem_subset_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum.eq_sumMaster_of_subset
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum.not_inj₀_subset_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum.not_inj₁_subset_inj₀

@[expose] public section

/-!
# Exercise 3.19 (Scott 1981, PRG-19, §3) — the sum functor `f + g`

Given approximable mappings `f : 𝒟₀ → 𝒟₀'` and `g : 𝒟₁ → 𝒟₁'`, Scott's Exercise 3.19 also asks for the
*sum* mapping `f + g : 𝒟₀ + 𝒟₁ → 𝒟₀' + 𝒟₁'`, characterized (equations (iii), (iv)) by

* `out₀ ∘ (f + g) ∘ in₀ = f`, and
* `out₁ ∘ (f + g) ∘ in₁ = g`.

We build `f + g` (`sumMap`) directly as a relation between sum-neighbourhoods: it routes the left copy
`0X` through `f` (to `0Y'`), the right copy `1Y` through `g` (to `1Y'`), and sends everything to the
master neighbourhood `{Λ} ∪ 0Δ₀' ∪ 1Δ₁'`. The disjointness of the two tagged copies (Exercise 3.18) is
exactly what makes this a well-defined approximable mapping — a left input can never produce a
right-tagged output, so there is no cross-contamination through `g(⊥)`.

Scott also asks whether (iii), (iv) *uniquely* determine `f + g`: they do **not**, because the behaviour
on the basepoint `Λ` (i.e. `(f + g)(⊥)`) is unconstrained; our choice sends `Λ` to `Λ`.

Everything is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
variable {h₀' : ∀ X, V₀'.mem X → X.Nonempty} {h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty}

/-! ### Structural extraction lemmas for sum-neighbourhoods. -/






/-! ### The sum mapping `f + g`. -/


/-! ### The defining identities (iii) and (iv). -/
end DomainTheory.NeighbourhoodSystems

/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324Iter.mapOfSeq
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324Iter.funIterEquiv
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324Iter.piCongrOrderIso
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324Iter.funIterIso
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324Iter.exists_forall_swap
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324Iter.toElementMap_mapOfSeq
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324Iter.projComp_mono
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324Iter.le_of_projComp_le

@[expose] public section

/-!
# Exercise 3.24(ii) (Scott 1981, PRG-19, §3) — `(𝒟₀ → 𝒟₁^∞) ≅ (𝒟₀ → 𝒟₁)^∞`

Using the infinite iterate `𝒟^∞` of Exercise 3.16 and the function space `(𝒟₀ → 𝒟₁)` of
Definition 3.8 / Theorem 3.10, we establish Scott's isomorphism (ii):

`(𝒟₀ → 𝒟₁^∞) ≅ (𝒟₀ → 𝒟₁)^∞`.

The crux is the order-isomorphism *on approximable maps*

`funIterEquiv : Hom(𝒟₀, 𝒟₁^∞) ≃o (ℕ → Hom(𝒟₀, 𝒟₁))`,

`f ↦ (n ↦ projₙ ∘ f)` with inverse the "infinite pairing" `g ↦ mapOfSeq g`, whose value is the
sequence `mapOfSeq g (x) = ⟨gₙ(x)⟩ₙ`. Transporting through Theorem 3.10's `funSpaceEquiv` (twice,
the second time pointwise via `OrderIso.piCongrRight`) and Exercise 3.16's `iterSeqEquiv` yields the
domain isomorphism.

Everything is **choice-free in spirit**; the only classical input is inherited from `Element.ext`,
`funSpaceEquiv` and the `choose` in the `∃/∀`-swap lemma, exactly as elsewhere in §3.
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}








end DomainTheory.NeighbourhoodSystems

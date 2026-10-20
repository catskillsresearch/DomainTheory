/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.RingTheory.Ideal.Span
import all Mathlib.RingTheory.Ideal.Span
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.IFamily
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.mem_IFamily

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Ring

open NeighborhoodSystem

variable {A : Type*} [CommRing A]

/-- Inclusion of neighbourhoods reversed to ideal generation: `I(F₁) ⊆ I(F₂) ↔ F₂ ⊆ ⟨F₁⟩`. -/
theorem IFamily_subset_iff (F₁ F₂ : Finset A) :
    IFamily F₁ ⊆ IFamily F₂ ↔ (↑F₂ : Set A) ⊆ Ideal.span (↑F₁ : Set A) := by
  constructor
  · intro h
    have hF₁ : F₁ ∈ IFamily F₁ := mem_IFamily.mpr Ideal.subset_span
    exact (h hF₁)
  · intro h G hG
    rw [mem_IFamily] at hG ⊢
    exact h.trans (SetLike.coe_subset_coe.mpr (Ideal.span_le.mpr hG))

end Ring

end DomainTheory.NeighbourhoodSystems

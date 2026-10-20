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
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.IFamily_subset_iff

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Ring

open NeighborhoodSystem

variable {A : Type*} [CommRing A]

theorem span_eq_of_IFamily_eq {F₁ F₂ : Finset A} (h : IFamily F₁ = IFamily F₂) :
    Ideal.span (↑F₁ : Set A) = Ideal.span (↑F₂ : Set A) := by
  have h12 : (↑F₂ : Set A) ⊆ Ideal.span (↑F₁ : Set A) :=
    (IFamily_subset_iff F₁ F₂).mp h.le
  have h21 : (↑F₁ : Set A) ⊆ Ideal.span (↑F₂ : Set A) :=
    (IFamily_subset_iff F₂ F₁).mp h.ge
  exact le_antisymm (Ideal.span_le.mpr h21) (Ideal.span_le.mpr h12)

end Ring

end DomainTheory.NeighbourhoodSystems

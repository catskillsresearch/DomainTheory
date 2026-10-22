/-ai
The filter of an ideal consists of the neighbourhoods I(F) whose generated ideal is contained in the ideal. The subfamily law forgets the containment. The master is I of the empty set, whose generated ideal is the bottom ideal and hence lies below the given ideal. The intersection of I(F₁) and I(F₂) is I of the union, and the span of a union is the supremum of the spans, which lies below the ideal when both spans do. Upward closure from I(F) to I(F') uses the inclusion criterion to place F' inside the span of F and therefore inside the ideal.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.IFamily
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.mem_IFamily
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.IFamily_subset_iff
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.IFamily_inter
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.ringSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.ringSystem_mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.mem_idealOf

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Ring

open NeighborhoodSystem

variable {A : Type*} [CommRing A]

variable [DecidableEq A]

/-- **Exercise 1.26 — the filter of an ideal.** `ofIdeal J = {I(F) ∣ ↑F ⊆ J}`. -/
def ofIdeal (J : Ideal A) : (ringSystem (A := A)).Element where
  mem S := ∃ F, S = IFamily F ∧ Ideal.span (↑F : Set A) ≤ J
  sub := by rintro S ⟨F, rfl, _⟩; exact ⟨F, rfl⟩
  master_mem := by
    refine ⟨∅, rfl, ?_⟩
    rw [Finset.coe_empty, Ideal.span_empty]
    exact bot_le
  inter_mem := by
    rintro X Y ⟨F₁, rfl, h₁⟩ ⟨F₂, rfl, h₂⟩
    refine ⟨F₁ ∪ F₂, IFamily_inter F₁ F₂, ?_⟩
    rw [Finset.coe_union, Ideal.span_union]
    exact sup_le h₁ h₂
  up_mem := by
    rintro X Y ⟨F, rfl, hF⟩ ⟨F', rfl⟩ hXY
    refine ⟨F', rfl, ?_⟩
    have hsub : (↑F' : Set A) ⊆ Ideal.span (↑F : Set A) := (IFamily_subset_iff F F').mp hXY
    exact (Ideal.span_le.mpr hsub).trans hF

end Ring

end DomainTheory.NeighbourhoodSystems

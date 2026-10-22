/-ai
The filter of the ideal of a filter equals the original filter.

By extensionality of elements. If the neighbourhood is I(F) and the span of F lies in the ideal of the filter, then each member of F lies in that span and hence in the ideal, so the singleton neighbourhoods belong to the filter, and the finite-intersection lemma puts I(F) in the filter. Conversely, the subfamily law writes the neighbourhood as I(F). The span lies in the ideal because each member of F has its singleton neighbourhood in the filter, by upward closure along the inclusion from the inclusion criterion, since the member lies in the span of F.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.mem_IFamily
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.IFamily_subset_iff
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.ringSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.ringSystem_mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.IFamily_mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.idealOf
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.mem_idealOf
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.mem_IFamily_of_forall
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.ofIdeal

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Ring

open NeighborhoodSystem

variable {A : Type*} [CommRing A]

variable [DecidableEq A]

theorem ofIdeal_idealOf (x : (ringSystem (A := A)).Element) : ofIdeal (idealOf x) = x := by
  apply NeighborhoodSystem.Element.ext
  intro S
  constructor
  · rintro ⟨F, rfl, hF⟩
    refine mem_IFamily_of_forall x F (fun a ha => ?_)
    have haspan : a ∈ Ideal.span (↑F : Set A) := Ideal.subset_span (by simpa using ha)
    exact mem_idealOf.mp (hF haspan)
  · intro hS
    obtain ⟨F, rfl⟩ := x.sub hS
    refine ⟨F, rfl, ?_⟩
    rw [Ideal.span_le]
    intro a ha
    rw [SetLike.mem_coe, mem_idealOf]
    refine x.up_mem hS (IFamily_mem {a}) ?_
    apply (IFamily_subset_iff _ _).mpr
    rw [Finset.coe_singleton, Set.singleton_subset_iff]
    exact Ideal.subset_span ha

end Ring

end DomainTheory.NeighbourhoodSystems

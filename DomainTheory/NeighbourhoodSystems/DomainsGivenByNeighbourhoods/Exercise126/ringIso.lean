/-ai
The order isomorphism from elements of the ring system to ideals sends a filter to its ideal and an ideal to its filter, with the two round trips given by the identities already proved. If the ideal of the first filter is contained in the ideal of the second and a neighbourhood belongs to the first, the subfamily law writes it as I(F). Each member of F lies in the ideal of the first filter, because upward closure and the inclusion criterion put the singleton neighbourhood in the filter, using that the member lies in the span of F. The ideal inclusion puts the member in the second ideal, and the finite-intersection lemma returns I(F). Conversely, if the first filter lies below the second, each singleton neighbourhood of a member of its ideal belongs to the second filter.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.RingTheory.Ideal.Span
import all Mathlib.RingTheory.Ideal.Span
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.IFamily
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.mem_IFamily
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.IFamily_subset_iff
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.ringSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.ringSystem_mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.IFamily_mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.idealOf
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.mem_idealOf
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.mem_IFamily_of_forall
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.ofIdeal
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.idealOf_ofIdeal
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.ofIdeal_idealOf

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Ring

open NeighborhoodSystem

variable {A : Type*} [CommRing A]

variable [DecidableEq A]

/-- **Exercise 1.26 — `|𝒟| ≅ (Ideals A, ⊆)`.** The domain of the ring's neighbourhood system is
order-isomorphic to the ideals of `A` ordered by inclusion, via `x ↦ {a ∣ I({a}) ∈ x}`. -/
def ringIso : (ringSystem (A := A)).Element ≃o Ideal A where
  toFun := idealOf
  invFun := ofIdeal
  left_inv := ofIdeal_idealOf
  right_inv := idealOf_ofIdeal
  map_rel_iff' := by
    intro x y
    constructor
    · intro h S hS
      obtain ⟨F, rfl⟩ := x.sub hS
      refine mem_IFamily_of_forall y F (fun a ha => ?_)
      have hax : a ∈ idealOf x := by
        rw [mem_idealOf]
        exact x.up_mem hS (IFamily_mem {a}) <| (IFamily_subset_iff _ _).mpr <| by
          rw [Finset.coe_singleton, Set.singleton_subset_iff]
          exact Ideal.subset_span (by simpa using ha)
      exact mem_idealOf.mp (h hax)
    · intro h a ha
      exact h (IFamily {a}) ha

end Ring

end DomainTheory.NeighbourhoodSystems

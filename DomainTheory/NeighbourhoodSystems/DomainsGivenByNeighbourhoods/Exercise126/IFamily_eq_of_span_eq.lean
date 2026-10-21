/-ai
If two finite sets generate the same ideal, they determine the same neighbourhood I(F).

The two inclusions of neighbourhoods each follow from the inclusion criterion, after rewriting the generated ideals by the hypothesis, which leaves the containment of a finite set in the ideal it generates.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.RingTheory.Ideal.Span
import all Mathlib.RingTheory.Ideal.Span
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Ring

open NeighborhoodSystem

variable {A : Type*} [CommRing A]





theorem IFamily_eq_of_span_eq {F₁ F₂ : Finset A}
    (h : Ideal.span (↑F₁ : Set A) = Ideal.span (↑F₂ : Set A)) : IFamily F₁ = IFamily F₂ := by
  apply Set.Subset.antisymm
  · exact (IFamily_subset_iff F₁ F₂).mpr (by rw [h]; exact Ideal.subset_span)
  · exact (IFamily_subset_iff F₂ F₁).mpr (by rw [← h]; exact Ideal.subset_span)

end Ring
end DomainTheory.NeighbourhoodSystems

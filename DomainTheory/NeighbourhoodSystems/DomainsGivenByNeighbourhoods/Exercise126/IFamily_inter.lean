/-ai
The intersection of I(F₁) and I(F₂) equals I of the union of F₁ and F₂.

By extensionality of sets. Unfolding I, membership in an intersection, the coercion of a union, and the criterion for containment of a union identifies the two sides.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.RingTheory.Ideal.Span
import all Mathlib.RingTheory.Ideal.Span
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.IFamily
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.mem_IFamily

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Ring

open NeighborhoodSystem

variable {A : Type*} [CommRing A]

variable [DecidableEq A]

/-- `I(F₁) ∩ I(F₂) = I(F₁ ∪ F₂)`: the system is closed under all binary intersections. -/
theorem IFamily_inter (F₁ F₂ : Finset A) :
    IFamily F₁ ∩ IFamily F₂ = IFamily (F₁ ∪ F₂) := by
  ext G
  simp only [IFamily, Set.mem_inter_iff, Set.mem_ofPred_eq, Finset.coe_union, Set.union_subset_iff]

end Ring

end DomainTheory.NeighbourhoodSystems

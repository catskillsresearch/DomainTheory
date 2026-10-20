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

variable [DecidableEq A]

/-- `I(F₁) ∩ I(F₂) = I(F₁ ∪ F₂)`: the system is closed under all binary intersections. -/
theorem IFamily_inter (F₁ F₂ : Finset A) :
    IFamily F₁ ∩ IFamily F₂ = IFamily (F₁ ∪ F₂) := by
  ext G
  simp only [IFamily, Set.mem_inter_iff, Set.mem_ofPred_eq, Finset.coe_union, Set.union_subset_iff]

end Ring

end DomainTheory.NeighbourhoodSystems

module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Order.UpperLower.Basic
import all Mathlib.Order.UpperLower.Basic
public import Mathlib.Order.Bounds.Basic
import all Mathlib.Order.Bounds.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.finalSegmentSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.mem_def
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.master_eq
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.exists_Ici_of_mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.lowerSetOf
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.lowerSetOf_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.lowerSetOf_isLowerSet
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.ofLowerSet

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace FinalSegment

open NeighborhoodSystem

variable {Δ : Type*} [LinearOrder Δ] [Nonempty Δ]

variable [WellFoundedLT Δ]

theorem ofLowerSet_lowerSetOf (x : (finalSegmentSystem Δ).Element) :
    ofLowerSet (lowerSetOf x) (lowerSetOf_nonempty x) (lowerSetOf_isLowerSet x) = x := by
  apply NeighborhoodSystem.Element.ext
  intro X
  constructor
  · rintro ⟨hX, a, haS, haX⟩
    exact x.up_mem haS hX haX
  · intro hX
    obtain ⟨a, rfl⟩ := exists_Ici_of_mem (x.sub hX)
    exact ⟨x.sub hX, a, hX, subset_rfl⟩

end FinalSegment

end DomainTheory.NeighbourhoodSystems

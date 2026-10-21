/-ai
The lower set of a filter in the final-segment system is a lower set.

If a token lies in the lower set and a second token lies below it, the principal upper set of the first belongs to the filter, the principal upper set of the second is a neighbourhood, and the first principal upper set is contained in the second. Upward closure puts the second principal upper set in the filter.
ai-/
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
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.Ici_mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.lowerSetOf

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace FinalSegment

open NeighborhoodSystem

variable {Δ : Type*} [LinearOrder Δ] [Nonempty Δ]

variable [WellFoundedLT Δ]

omit [WellFoundedLT Δ] in
theorem lowerSetOf_isLowerSet (x : (finalSegmentSystem Δ).Element) :
    IsLowerSet (lowerSetOf x) := by
  intro a b hba ha
  exact x.up_mem ha (Ici_mem b) (Set.Ici_subset_Ici.mpr hba)

end FinalSegment

end DomainTheory.NeighbourhoodSystems

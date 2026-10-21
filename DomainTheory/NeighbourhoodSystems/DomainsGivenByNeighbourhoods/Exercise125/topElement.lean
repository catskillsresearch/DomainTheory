/-ai
The greatest element of the final-segment system is the filter of all neighbourhoods. Subfamily membership is the neighbourhood predicate. The master belongs because the whole token set is a nonempty upper set. The intersection of two neighbourhoods equals one of them, since any two upper sets are nested: when the first is contained in the second the intersection equals the first, and when the second is contained in the first the intersection equals the second. Upward closure returns the larger neighbourhood.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Order.UpperLower.Basic
import all Mathlib.Order.UpperLower.Basic
public import Mathlib.Order.Bounds.Basic
import all Mathlib.Order.Bounds.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.upperSet_subset_or
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.finalSegmentSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.mem_def
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.master_eq

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace FinalSegment

open NeighborhoodSystem

variable {Δ : Type*} [LinearOrder Δ] [Nonempty Δ]

variable [WellFoundedLT Δ]

omit [WellFoundedLT Δ]

/-- The greatest element: the filter of **all** neighbourhoods. -/
def topElement : (finalSegmentSystem Δ).Element where
  mem X := (finalSegmentSystem Δ).mem X
  sub h := h
  master_mem := ⟨Set.univ_nonempty, isUpperSet_univ⟩
  inter_mem := by
    rintro X Y hX hY
    rcases upperSet_subset_or hX.2 hY.2 with h | h
    · rw [Set.inter_eq_left.mpr h]; exact hX
    · rw [Set.inter_eq_right.mpr h]; exact hY
  up_mem := fun _ hY _ => hY

end FinalSegment

end DomainTheory.NeighbourhoodSystems

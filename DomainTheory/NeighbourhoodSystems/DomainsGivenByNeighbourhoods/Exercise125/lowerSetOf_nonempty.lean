/-ai
The lower set of a filter in the final-segment system is nonempty.

Apply exists_Ici_of_mem to the whole token set, using that it is a nonempty upper set, and rewrite that set as a principal upper set of some token. The master belongs to the filter, and rewriting the membership by that equality shows that the token lies in the lower set.
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
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.exists_Ici_of_mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.lowerSetOf

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace FinalSegment

open NeighborhoodSystem

variable {Δ : Type*} [LinearOrder Δ] [Nonempty Δ]

variable [WellFoundedLT Δ]

theorem lowerSetOf_nonempty (x : (finalSegmentSystem Δ).Element) : (lowerSetOf x).Nonempty := by
  obtain ⟨a, ha⟩ := exists_Ici_of_mem (X := (Set.univ : Set Δ)) ⟨Set.univ_nonempty, isUpperSet_univ⟩
  refine ⟨a, ?_⟩
  have hu : x.mem (Set.univ) := x.master_mem
  rw [ha] at hu
  exact hu

end FinalSegment

end DomainTheory.NeighbourhoodSystems

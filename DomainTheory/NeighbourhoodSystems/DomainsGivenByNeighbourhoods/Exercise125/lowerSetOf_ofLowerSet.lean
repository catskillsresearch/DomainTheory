/-ai
For a nonempty lower set, the lower set of its associated filter is the original set.

By extensionality of sets. If a token lies in the lower set of the filter, the membership supplies a member of the original set whose principal upper set is contained in the principal upper set of the token. That inclusion gives the inequality, and the lower-set law returns the token. If the token lies in the original set, its principal upper set is a neighbourhood and contains itself.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Order.Bounds.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.mem_def
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.master_eq
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.Ici_mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.lowerSetOf
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.ofLowerSet

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace FinalSegment

open NeighborhoodSystem

variable {Δ : Type*} [LinearOrder Δ] [Nonempty Δ]

variable [WellFoundedLT Δ]

omit [WellFoundedLT Δ] in
theorem lowerSetOf_ofLowerSet (S : Set Δ) (hSne : S.Nonempty) (hS : IsLowerSet S) :
    lowerSetOf (ofLowerSet S hSne hS) = S := by
  ext a
  constructor
  · rintro ⟨_, b, hbS, hba⟩
    exact hS (Set.Ici_subset_Ici.mp hba) hbS
  · intro ha
    exact ⟨Ici_mem a, a, ha, subset_rfl⟩

end FinalSegment

end DomainTheory.NeighbourhoodSystems

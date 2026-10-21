/-ai
The final-segment neighbourhood system on a nonempty linear order consists of the nonempty upper sets, with the whole token set as master. It is obtained from the nested-or-disjoint construction. The whole set is a nonempty upper set. Any two upper sets are nested, and that nesting supplies the nested-or-disjoint law. Every such set is contained in the whole set.
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

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace FinalSegment

open NeighborhoodSystem

/-- **Exercise 1.25 — the final-segment neighbourhood system.** Over a (non-empty) linear order
`Δ`, the non-empty upper sets (final segments) form a neighbourhood system. Built via
`ofNestedOrDisjoint` since any two upper sets are nested (`upperSet_subset_or`). -/
def finalSegmentSystem (Δ : Type*) [LinearOrder Δ] [Nonempty Δ] : NeighborhoodSystem Δ :=
  NeighborhoodSystem.ofNestedOrDisjoint
    (fun X => X.Nonempty ∧ IsUpperSet X)
    Set.univ
    Set.univ_nonempty
    ⟨Set.univ_nonempty, isUpperSet_univ⟩
    (fun _ _ hX hY => (upperSet_subset_or hX.2 hY.2).imp_right Or.inl)
    (fun _ => Set.subset_univ _)

end FinalSegment

end DomainTheory.NeighbourhoodSystems

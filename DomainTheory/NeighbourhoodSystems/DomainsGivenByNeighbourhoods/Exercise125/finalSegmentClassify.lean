/-ai
The classification of the final-segment domain is the order isomorphism from its elements to the nonempty lower sets of the well-order. It sends an element to the set of points whose principal final segment belongs to the element, and the inverse sends a nonempty lower set to the associated element. The two round trips are the supplied inverse lemmas. One element approximates another if and only if the associated lower set is contained in the other: a neighbourhood is some principal final segment, so membership passes across that containment, and membership of a principal final segment passes across approximation.
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
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.lowerSetOf_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.lowerSetOf_isLowerSet
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.ofLowerSet
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.lowerSetOf_ofLowerSet
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.ofLowerSet_lowerSetOf

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace FinalSegment

open NeighborhoodSystem

variable {Δ : Type*} [LinearOrder Δ] [Nonempty Δ]

variable [WellFoundedLT Δ]

/-- **Exercise 1.25 — classification of `|𝒟|`.** For a well-order `Δ`, the domain of non-empty
final segments is order-isomorphic to the poset of **non-empty initial segments** (lower sets) of
`Δ` under inclusion: `x ↦ {a ∣ Ici a ∈ x}`. (So `|𝒟|` is the lattice of cuts of `Δ`.) -/
def finalSegmentClassify :
    (finalSegmentSystem Δ).Element ≃o {S : Set Δ // S.Nonempty ∧ IsLowerSet S} where
  toFun x := ⟨lowerSetOf x, lowerSetOf_nonempty x, lowerSetOf_isLowerSet x⟩
  invFun S := ofLowerSet S.1 S.2.1 S.2.2
  left_inv x := ofLowerSet_lowerSetOf x
  right_inv S := Subtype.ext (lowerSetOf_ofLowerSet S.1 S.2.1 S.2.2)
  map_rel_iff' := by
    intro x y
    constructor
    · intro h X hX
      obtain ⟨a, rfl⟩ := exists_Ici_of_mem (x.sub hX)
      exact h hX
    · intro h a ha
      exact h _ ha

end FinalSegment

end DomainTheory.NeighbourhoodSystems

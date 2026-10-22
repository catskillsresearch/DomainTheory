module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Order.Bounds.Basic
public import Mathlib.Tactic
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

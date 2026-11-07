module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.FinalSegment

@[expose] public section

open DomainTheory.NeighbourhoodSystems
open DomainTheory.NeighbourhoodSystems.FinalSegment
variable {Δ : Type*} [LinearOrder Δ] [Nonempty Δ]

/-- Scott's Exercise 1.25: final-segment systems have a top total element, not principal
    when the order has no maximum. -/
theorem exercise_1_25 :
    (finalSegmentSystem Δ).IsTotal topElement ∧
      (∀ (_hnomax : ∀ a : Δ, ∃ b, a < b) (a : Δ),
        topElement ≠ (finalSegmentSystem Δ).principal (Ici_mem a)) :=
  ⟨topElement_isTotal, topElement_not_principal_of_noMax⟩

module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.powersetIso

@[expose] public section

open DomainTheory.NeighbourhoodSystems

open PowersetIso

/-- Scott's Exercise 5.13 (powerset clause): order isomorphisms among
`Set ℕ`, `Set (ℕ × ℕ)`, and `Set ℕ × Set ℕ`. -/
theorem example_513b :
    Nonempty (Set ℕ ≃o Set (ℕ × ℕ)) ∧
    Nonempty (Set ℕ ≃o Set ℕ × Set ℕ) ∧
    Nonempty (Set (ℕ × ℕ) ≃o Set ℕ × Set ℕ) :=
  ⟨⟨PN_orderIso_PNN⟩, ⟨PN_orderIso_prod⟩, ⟨PNN_orderIso_prod⟩⟩


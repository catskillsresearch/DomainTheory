module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.reprSystem

@[expose] public section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set
open ReprSystem

/-- Scott's Exercise 2.22: a family closed under nonempty intersections and directed unions is
    inclusion-isomorphic to the domain of its token neighbourhood system. -/
theorem example_222 {τ : Type*} (C : Set (Set τ))
    (hInter : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → ⋂₀ 𝒮 ∈ C)
    (hne : C.Nonempty)
    (hDir : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → DirectedOn (· ⊆ ·) 𝒮 → ⋃₀ 𝒮 ∈ C) :
    Nonempty ((reprSystem C hInter hne).Element ≃o {X : Set τ // X ∈ C}) :=
  ⟨reprIso C hInter hne hDir⟩

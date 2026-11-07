module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Ring

@[expose] public section

open DomainTheory.NeighbourhoodSystems
open DomainTheory.NeighbourhoodSystems.Ring
variable {A : Type*} [CommRing A] [DecidableEq A]

/-- Scott's Exercise 1.26: ideal neighbourhood families depend only on the spanned ideal. -/
theorem exercise_1_26 {F₁ F₂ : Finset A}
    (h : Ideal.span (↑F₁ : Set A) = Ideal.span (↑F₂ : Set A)) : IFamily F₁ = IFamily F₂ :=
  IFamily_eq_of_span_eq h

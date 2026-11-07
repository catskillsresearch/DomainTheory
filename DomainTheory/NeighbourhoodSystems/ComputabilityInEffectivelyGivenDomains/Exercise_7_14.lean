module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.computableWitness

@[expose] public section

open DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive DomainTheory.NeighbourhoodSystems
open DomainTheory.NeighbourhoodSystems.ComputableWitness
/-- Scott's Exercise 7.14: computable elements are decreasing unions of principals. -/
theorem example_714 :
    ∀ {β : Type*} {W : NeighborhoodSystem β} (Q : ComputablePresentation W) {y : W.Element},
      ComputableElement Q y →
        ∃ t : ℕ → ℕ, Nat.Primrec t ∧
          (∀ i, Q.X (t (i + 1)) ⊆ Q.X (t i)) ∧
          (∀ Z, y.mem Z ↔ ∃ i, (W.principal (Q.mem_X (t i))).mem Z) :=
  @computableElement_eq_decreasing_iUnion_principal


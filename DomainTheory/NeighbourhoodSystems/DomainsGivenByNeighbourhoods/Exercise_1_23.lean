module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.GreedyEnum

@[expose] public section

open DomainTheory.NeighbourhoodSystems
open DomainTheory.NeighbourhoodSystems.GreedyEnum
open NeighborhoodSystem
variable {α : Type*} (V : NeighborhoodSystem α) (enum : ℕ → Set α) [DecidablePred V.mem]
variable (henum : ∀ n, V.mem (enum n))
variable (hsurj : ∀ {X : Set α}, V.mem X → ∃ n, enum n = X)
include henum hsurj

/-- Scott's Exercise 1.23: greedy neighbourhoods are finitely consistent; the greedy
    element is total when the enumeration is surjective; every filter is sequence-determined. -/
theorem exercise_1_23 :
    (∀ n, V.Consistent (Y V enum) n) ∧
      V.IsTotal (greedyElement V enum henum) ∧
      ∀ x : V.Element,
        ∃ s : ℕ → Set α, (∀ n, V.mem (s n)) ∧ ∀ Z, x.mem Z ↔ (V.mem Z ∧ ∃ n, s n ⊆ Z) :=
  ⟨Y_prefix_consistent V enum henum, greedyElement_isTotal V enum henum hsurj,
    filters_sequence_determined V enum henum hsurj⟩

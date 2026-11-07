module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.RatInterval

@[expose] public section

open DomainTheory.NeighbourhoodSystems
open DomainTheory.NeighbourhoodSystems.RatInterval
/-- Scott's Exercise 1.17: rational open intervals separate reals and are intersection-closed
    on nonempty meets. -/
theorem exercise_1_17 :
    (∀ {s t : ℝ}, filterAt s = filterAt t → s = t) ∧
      (∀ {X Y : Set ℝ}, ratIntervalMem X → ratIntervalMem Y → (X ∩ Y).Nonempty →
        ratIntervalMem (X ∩ Y)) :=
  ⟨filterAt_injective, inter_mem'⟩


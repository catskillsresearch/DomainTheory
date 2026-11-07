module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.NeighborhoodSystem_more
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.TriSys

@[expose] public section

open DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem
open DomainTheory.NeighbourhoodSystems.TriSys
/-- Scott's Exercise 1.18: least filters for finitely consistent families, and a counterexample. -/
theorem exercise_1_18 :
    (∀ {α : Type*} (V : NeighborhoodSystem α) (C : Set (Set α))
        (hCsub : ∀ X ∈ C, V.mem X) (hC : V.FinitelyConsistent C) (z : V.Element),
      (∀ W ∈ C, z.mem W) → V.leastFilter C hCsub hC ≤ z) ∧
      ¬ system.FinitelyConsistent family :=
  ⟨NeighborhoodSystem.leastFilter_le, not_finitelyConsistent⟩

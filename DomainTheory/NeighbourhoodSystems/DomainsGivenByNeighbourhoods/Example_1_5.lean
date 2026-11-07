module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.P4

@[expose] public section

open DomainTheory.NeighbourhoodSystems
open P4

theorem example_1_5 :
    ∃ (V : NeighborhoodSystem Token),
      V.master = (Set.univ : Set Token) ∧
        (∀ X : Set Token, V.mem X ↔ X.Nonempty) :=
  ⟨neighborhoodSystem, rfl, fun _ => Iff.rfl⟩

module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.BinTree

@[expose] public section

open DomainTheory.NeighbourhoodSystems
open BinTree

theorem example_1_4 :
    ∃ (V : NeighborhoodSystem Token),
      V.master = (Set.univ : Set Token) ∧
        (∀ X : Set Token,
          V.mem X ↔
            X = Set.univ ∨ X = left ∨ X = right ∨
              X = leaf00 ∨ X = leaf01 ∨ X = leaf10 ∨ X = leaf11) :=
  ⟨neighborhoodSystem, rfl, fun _ => Iff.rfl⟩

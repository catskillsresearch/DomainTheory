module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ThreeToken

@[expose] public section

open DomainTheory.NeighbourhoodSystems
open ThreeToken

theorem example_1_3 :
    ∃ (V : NeighborhoodSystem Token),
      V.master = (Set.univ : Set Token) ∧
        (∀ X : Set Token,
          V.mem X ↔
            X = Set.univ ∨ X = ({1, 2} : Set Token) ∨ X = ({2} : Set Token)) :=
  ⟨neighborhoodSystem, rfl, fun X => by
    have h12 : twelve = ({1, 2} : Set Token) := by
      ext t; fin_cases t <;> simp [twelve]
    refine (mem_iff X).trans ?_
    simp [master, two, h12]⟩

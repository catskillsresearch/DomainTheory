module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.TwoToken

@[expose] public section

open DomainTheory.NeighbourhoodSystems
open TwoToken

/-- **Example 1.2.** Tokens `Δ = {0, 1}` and neighbourhoods `𝒟 = {{0, 1}, {0}, {1}}`
form a neighbourhood system. -/
theorem example_1_2 :
    ∃ (V : NeighborhoodSystem Token),
      V.master = (Set.univ : Set Token) ∧
        (∀ X : Set Token,
          V.mem X ↔ X = Set.univ ∨ X = ({0} : Set Token) ∨ X = ({1} : Set Token)) :=
  ⟨neighborhoodSystem, rfl, fun X => (mem_iff X).trans (by simp [master, zero, one])⟩

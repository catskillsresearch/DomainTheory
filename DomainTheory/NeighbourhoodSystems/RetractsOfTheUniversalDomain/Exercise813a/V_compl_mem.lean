module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812g4
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a.levelSet_compl

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem


theorem V_compl_mem {X : Set ℕ} (hX : V.mem X) : Xᶜ = ∅ ∨ V.mem Xᶜ := by
  obtain ⟨k, m, rfl, -⟩ := hX
  rw [levelSet_compl]
  rcases (levelSet _ _).eq_empty_or_nonempty with h | h
  · exact Or.inl h
  · exact Or.inr ⟨k, _, rfl, h⟩

end DomainTheory.NeighbourhoodSystems

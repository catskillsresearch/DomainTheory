module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.levelSet_diff

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem



/-- **`V` is closed under set-difference of two of its own neighbourhoods** (or the difference is
empty). -/
theorem V_diff_mem {X Y : Set ℕ} (hX : V.mem X) (hY : V.mem Y) : X \ Y = ∅ ∨ V.mem (X \ Y) := by
  obtain ⟨k₁, m₁, rfl, -⟩ := hX
  obtain ⟨k₂, m₂, rfl, -⟩ := hY
  rcases Set.eq_empty_or_nonempty (levelSet k₁ m₁ \ levelSet k₂ m₂) with h | h
  · exact Or.inl h
  · exact Or.inr ⟨max k₁ k₂, _, levelSet_diff k₁ m₁ k₂ m₂, h⟩

end DomainTheory.NeighbourhoodSystems

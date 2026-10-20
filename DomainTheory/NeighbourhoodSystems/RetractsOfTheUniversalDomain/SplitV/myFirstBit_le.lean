module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.MinLevel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitV.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive







/-- **`myFirstBit` never overshoots its bound.** -/
theorem myFirstBit_le (m N : ℕ) : myFirstBit m N ≤ N := by
  rcases myFirstBit_spec m N with ⟨h, -, -⟩ | ⟨h, -⟩ <;> omega

end DomainTheory.NeighbourhoodSystems

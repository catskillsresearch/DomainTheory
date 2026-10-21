/-ai
The left-hand and right-hand pieces of the canonical split are disjoint.

Rewrite both pieces as the neighbourhood cut by the open ray below the midpoint and the closed ray from the midpoint. A point of both would lie strictly below the midpoint and at least at the midpoint.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.splitU2Left
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.splitU2Right
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.UX_splitU2Left
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.UX_splitU2Right

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **Disjointness**: `splitU2Left`/`splitU2Right` cover disjoint pieces. -/
theorem splitU2_disjoint (n : ℕ) : UX (splitU2Left n) ∩ UX (splitU2Right n) = ∅ := by
  rw [UX_splitU2Left, UX_splitU2Right]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ici, Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨-, h1⟩, -, h2⟩
  exact absurd h1 (not_lt.mpr h2)

end DomainTheory.NeighbourhoodSystems

/-ai
The left-hand and right-hand pieces of the canonical split reunite to the original neighbourhood.

Rewrite both pieces as cuts of the neighbourhood by the open ray below the midpoint and the closed ray from the midpoint. A point of either cut lies in the neighbourhood. A point of the neighbourhood lies strictly below the midpoint or at least at the midpoint, and those two cases are the two cuts.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.splitU2MidCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.splitU2Left
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.splitU2Right
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.UX_splitU2Left
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.UX_splitU2Right

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **Covering**: `splitU2Left`/`splitU2Right` reunite to `Xₙ`. -/
theorem splitU2_union (n : ℕ) : UX (splitU2Left n) ∪ UX (splitU2Right n) = UX n := by
  rw [UX_splitU2Left, UX_splitU2Right]
  ext x
  simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ici]
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
  · intro h
    rcases lt_or_ge x (decodeRat (splitU2MidCode n)) with hlt | hge
    · exact Or.inl ⟨h, hlt⟩
    · exact Or.inr ⟨h, hge⟩

end DomainTheory.NeighbourhoodSystems

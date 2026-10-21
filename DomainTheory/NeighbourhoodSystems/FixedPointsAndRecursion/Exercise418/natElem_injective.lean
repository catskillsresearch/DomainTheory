/-ai
Equal numerals name equal natural numbers.

The singleton of the first index belongs to the first numeral and hence to the second. By the membership law for numerals, that neighbourhood is the whole token set, which a singleton is not, or it is the singleton of the second index, and equal singletons have equal indices.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise418.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise418

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap Example43


/-- **Exercise 4.18 (Scott 1981, PRG-19).** The numerals are distinct: `n̂ = m̂ ⟹ n = m`. -/
theorem natElem_injective {n m : ℕ} (h : natElem n = natElem m) : n = m := by
  have hmem : (natElem m).mem {n} := h ▸ (mem_natElem_iff.mpr (Or.inr rfl))
  rw [mem_natElem_iff] at hmem
  rcases hmem with hu | hs
  · exact absurd hu (singleton_ne_univ n)
  · exact singleton_nat_inj hs

end DomainTheory.NeighbourhoodSystems.Exercise418

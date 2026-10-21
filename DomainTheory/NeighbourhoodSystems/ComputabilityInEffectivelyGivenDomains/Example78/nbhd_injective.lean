/-ai
If two cofinite neighbourhoods are equal, then their indices are equal.

Equality of the sets gives, at each bit position, the same condition that the bit is unset. Comparing the two bit values in all four combinations yields equal bits, so the numbers are equal.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78.nbhd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78.mem_nbhd

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example78

open Domain.Recursive NeighborhoodSystem

/-- The enumeration `n ↦ nbhd n` is **one-one** (Scott's converse-ordered neighbourhoods are in
bijection with the indices): from `nbhd n = nbhd m` we recover `n = m` bit by bit. -/
theorem nbhd_injective {n m : ℕ} (h : nbhd n = nbhd m) : n = m := by
  apply Nat.eq_of_testBit_eq
  intro k
  have hk : (n.testBit k = false) ↔ (m.testBit k = false) := by
    have := Set.ext_iff.mp h k; simpa only [mem_nbhd] using this
  cases hn : n.testBit k <;> cases hm : m.testBit k <;> simp_all

end DomainTheory.NeighbourhoodSystems.Example78

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.lowXor
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.lowXor_eq_mod

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.mem_ne_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.union_mem_or_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.UnionClosed
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- One recursion step for `Nat.xor` on the low bit: `x ^^^ y = 2 (x/2 ^^^ y/2) + lowXor x y`. -/
theorem xor_low_rec (x y : ℕ) : x ^^^ y = 2 * (x / 2 ^^^ y / 2) + lowXor x y := by
  have hdiv : (x ^^^ y) / 2 = x / 2 ^^^ y / 2 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [← Nat.testBit_add_one, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_add_one,
      Nat.testBit_add_one]
  have hmod := lowXor_eq_mod x y
  conv_lhs => rw [← Nat.div_add_mod (x ^^^ y) 2]
  rw [hdiv, hmod]

end DomainTheory.NeighbourhoodSystems

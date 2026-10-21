/-ai
The exclusive disjunction of x and y equals twice the exclusive disjunction of their halves, plus their low-bit exclusive disjunction.

The quotient of the exclusive disjunction by 2 equals the exclusive disjunction of the quotients, by comparing bits: the bit at position i of the quotient is the bit at position i + 1 of the exclusive disjunction, which splits as the exclusive disjunction of the bits at position i + 1 and hence of the bits at position i of the two quotients. The low-bit operation equals the exclusive disjunction modulo 2. Rewriting the left-hand side by the division-remainder decomposition modulo 2, and then by these two identities, gives the claim.
ai-/
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

set_option linter.unusedSectionVars false

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

/-ai
Bitwise conjunction satisfies the one-step recursion that the conjunction of two numbers
equals twice the conjunction of their halves plus their low-bit conjunction.

The quotient by two of the conjunction equals the conjunction of the quotients, because
the two sides have the same test bits after shifting the index by one and using the
test-bit law for conjunction. The low-bit conjunction equals the remainder of the
conjunction modulo two. Rewriting the left side by division and remainder, and
substituting those two identities, gives the recursion.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.lowAnd
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.lowAnd_eq_mod

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.V_no_minimal
@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- One recursion step for `Nat.land` on the low bit: `x &&& y = 2 (x/2 &&& y/2) + lowAnd x y`. -/
theorem land_low_rec (x y : ℕ) : x &&& y = 2 * (x / 2 &&& y / 2) + lowAnd x y := by
  have hdiv : (x &&& y) / 2 = x / 2 &&& y / 2 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [← Nat.testBit_add_one, Nat.testBit_and, Nat.testBit_and, Nat.testBit_add_one,
      Nat.testBit_add_one]
  have hmod := lowAnd_eq_mod x y
  conv_lhs => rw [← Nat.div_add_mod (x &&& y) 2]
  rw [hdiv, hmod]

end DomainTheory.NeighbourhoodSystems

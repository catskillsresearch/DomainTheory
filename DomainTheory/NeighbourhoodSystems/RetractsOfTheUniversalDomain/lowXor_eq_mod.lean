/-ai
The low-bit exclusive disjunction of x and y equals their bitwise exclusive disjunction modulo 2.

Unfold the arithmetic form, rewrite by the formula for exclusive disjunction modulo 2, and use the symmetric form of addition modulo 2.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.lowXor

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- `lowXor x y = (x ^^^ y) % 2`. -/
theorem lowXor_eq_mod (x y : ℕ) : lowXor x y = (x ^^^ y) % 2 := by
  unfold lowXor
  rw [Nat.xor_mod_two_eq]
  exact (Nat.add_mod x y 2).symm

end DomainTheory.NeighbourhoodSystems

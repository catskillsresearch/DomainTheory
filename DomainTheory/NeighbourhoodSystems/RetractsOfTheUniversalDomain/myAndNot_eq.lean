/-ai
The and-not of a and b equals the exclusive disjunction of a with the conjunction of a and b.

Unfold and-not and rewrite by the equations for the iterative exclusive disjunction and the iterative conjunction.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.myXor_eq_xor
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.myAndNot

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem myAndNot_eq (a b : ℕ) : myAndNot a b = a ^^^ (a &&& b) := by
  unfold myAndNot; rw [myXor_eq_xor, myLand_eq_land]

end DomainTheory.NeighbourhoodSystems

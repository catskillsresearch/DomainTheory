/-ai
The iterative bitwise conjunction equals the bitwise conjunction.

Unfolding the iteration, the accumulator clause of the iteration invariant at a number
of steps equal to the sum of the arguments is used. Each argument divided by two to that
power is zero, because each is strictly below two to its own power and that power is at
most two to the power of the sum. Substituting those zeros, simplification leaves the
conjunction.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myLand
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.landStep_iter_spec

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.V_no_minimal
@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **Correctness of the iterative bitwise AND.** `myLand a b = a &&& b`. -/
theorem myLand_eq_land (a b : ℕ) : myLand a b = a &&& b := by
  unfold myLand
  obtain ⟨_, _, _, hAcc⟩ := landStep_iter_spec a b (a + b)
  have ha0 : a / 2 ^ (a + b) = 0 :=
    Nat.div_eq_of_lt (Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by decide)
      (Nat.le_add_right a b)))
  have hb0 : b / 2 ^ (a + b) = 0 :=
    Nat.div_eq_of_lt (Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by decide)
      (Nat.le_add_left b a)))
  rw [ha0, hb0] at hAcc
  simpa using hAcc

end DomainTheory.NeighbourhoodSystems

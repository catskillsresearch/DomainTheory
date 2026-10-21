/-ai
The bit test of a position in a natural number is the remainder modulo two of that
number divided by two to the power of the position, a value in {0, 1} agreeing with the
characterization of the test bit as the decision that this remainder equals one.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myDivPow2

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- `myTestBit m ℓ ∈ {0,1}` is a `Nat.Primrec` version of `m.testBit ℓ`
(`myTestBit_eq_one_iff`), via `myDivPow2` and mathlib's own
`Nat.testBit_eq_decide_div_mod_eq : m.testBit ℓ = decide (m / 2 ^ ℓ % 2 = 1)`. -/
def myTestBit (m ℓ : ℕ) : ℕ := myDivPow2 m ℓ % 2

end DomainTheory.NeighbourhoodSystems

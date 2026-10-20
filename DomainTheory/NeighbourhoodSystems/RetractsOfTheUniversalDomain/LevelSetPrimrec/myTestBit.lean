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

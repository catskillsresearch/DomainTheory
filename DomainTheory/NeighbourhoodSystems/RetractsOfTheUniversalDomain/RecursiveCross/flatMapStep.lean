/-ai
The fold step for flatMapCode pops y from the packed argument and appends f of the pair of the fixed parameter x and y onto the accumulator.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross.appendCode

@[expose] public section

namespace Domain.Recursive

/-- `foldCode`'s step for `flatMapCode`: pops `y` from the folded list, appends `f (pair x y)`
(`x` threaded as the fixed parameter) onto the accumulator. -/
def flatMapStep (f : ℕ → ℕ) (w : ℕ) : ℕ :=
  appendCode (f (Nat.pair w.unpair.2.unpair.2 w.unpair.1)) w.unpair.2.unpair.1

end Domain.Recursive

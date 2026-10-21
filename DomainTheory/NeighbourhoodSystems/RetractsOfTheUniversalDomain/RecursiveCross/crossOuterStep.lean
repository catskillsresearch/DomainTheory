/-ai
The outer step of the coded fold pops the head x from the packed argument, computes the inner cross of that head with the fixed list code, and appends the result onto the accumulator.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross.appendCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross.crossInner

@[expose] public section

namespace Domain.Recursive

/-- `foldCode`'s outer step: pops `x` from `c1`, appends `crossInner bop x c2` onto the
accumulator (`c2` threaded as the fixed parameter). -/
def crossOuterStep (bop : ℕ → ℕ) (w : ℕ) : ℕ :=
  appendCode (crossInner bop w.unpair.1 w.unpair.2.unpair.2) w.unpair.2.unpair.1

end Domain.Recursive

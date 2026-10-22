module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive

@[expose] public section

namespace Domain.Recursive

/-- `foldCode`'s step for the inner loop: pops `y` from `c2`, applies `bop (pair x y)` (`x` threaded
as the fixed parameter), conses onto the accumulator. -/
def crossInnerStep (bop : ℕ → ℕ) (w : ℕ) : ℕ :=
  Nat.pair (bop (Nat.pair w.unpair.2.unpair.2 w.unpair.1)) w.unpair.2.unpair.1 + 1

end Domain.Recursive

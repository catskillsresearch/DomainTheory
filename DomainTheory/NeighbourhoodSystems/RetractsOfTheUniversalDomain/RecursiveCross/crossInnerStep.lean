/-ai
The inner step reads a code as an element, an accumulator, and a fixed first argument, applies the binary operation to the pair of that argument and the element, and returns one more than the pair of the result and the accumulator.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive

@[expose] public section

namespace Domain.Recursive

/-- `foldCode`'s step for the inner loop: pops `y` from `c2`, applies `bop (pair x y)` (`x` threaded
as the fixed parameter), conses onto the accumulator. -/
def crossInnerStep (bop : ℕ → ℕ) (w : ℕ) : ℕ :=
  Nat.pair (bop (Nat.pair w.unpair.2.unpair.2 w.unpair.1)) w.unpair.2.unpair.1 + 1

end Domain.Recursive

/-ai
A set of natural numbers, viewed as an element of the lattice of all such sets, is recursively enumerable when membership in it is a recursively enumerable predicate on the natural numbers.
ai-/
module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

/-- Recursively enumerable subsets of `ω`, as elements of `Pω`. -/
class IsRE (u : Pomega) : Prop where
  out : REPred fun n : ℕ => n ∈ u

end DomainTheory.DataTypesAsLattices

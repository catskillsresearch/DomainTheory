/-ai
Selection on a {0,1} condition c between a and b is the arithmetic combination of c times a and one minus c times b. It returns a when c is 1 and b when c is 0.
ai-/
module

public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Data.Nat.Pairing
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.List.Basic
public import Mathlib.Computability.Partrec
public import Mathlib.Tactic.Ring
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.unpair_pair_fst
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.unpair_pair_snd

@[expose] public section

namespace Domain.Recursive

/-- Choice-free primitive-recursive **selection**: `selectFn c a b = a` if `c = 1`, `= b` if `c = 0`
(for a `{0,1}`-valued `c`), via `c * a + (1 - c) * b`. -/
def selectFn (c a b : ℕ) : ℕ := c * a + (1 - c) * b

end Domain.Recursive

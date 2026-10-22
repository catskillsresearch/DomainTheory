/-ai
The witness-threading fold step takes an accumulator that pairs a remaining witness code with a flag, and a list head. It replaces the remaining code by the second component of the unpairing of that code minus one, and replaces the flag by the conjunction of the old flag with the equality-to-one test of the predicate at the pair of the popped witness and the head. The popped witness is the first component of that same unpairing.
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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.selectFn
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.selectFn_one
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.selectFn_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.selectFn_ite
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.isOne
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.isOne_one
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.isOne_zero

@[expose] public section

namespace Domain.Recursive

/-- The pure (set-theoretic) witness-threading fold step. The accumulator is `pair remWitness flag`:
at the list head `x` we pop a witness `i` (the `decodeList` head of `remWitness`, i.e.
`(remWitness - 1).unpair.1`) with new remaining code `(remWitness - 1).unpair.2`, and `AND` the flag
with `isOne (qc ⟨i, x⟩)`. -/
def reForallF (qc : ℕ → ℕ) (acc x : ℕ) : ℕ :=
  Nat.pair (acc.unpair.1 - 1).unpair.2
    (selectFn acc.unpair.2 (isOne (qc (Nat.pair (acc.unpair.1 - 1).unpair.1 x))) 0)

end Domain.Recursive

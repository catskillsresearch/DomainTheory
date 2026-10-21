/-ai
The half-parity of a natural is the pair of its quotient by 2 and its residue modulo 2. It is built by recursion from 0, and the value at the next number is the pair of the old quotient plus the old residue and of 1 minus the old residue, the carry from an odd number to the next even number.
ai-/
module

public import Mathlib.Data.Nat.Sqrt
import all Mathlib.Data.Nat.Sqrt
public import Mathlib.Data.Nat.Pairing
import all Mathlib.Data.Nat.Pairing
public import Mathlib.Data.Nat.Bitwise
import all Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.List.Basic
import all Mathlib.Data.List.Basic
public import Mathlib.Computability.Partrec
import all Mathlib.Computability.Partrec
public import Mathlib.Tactic.Ring
import all Mathlib.Tactic.Ring
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.unpair_pair_fst
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.unpair_pair_snd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.selectFn_one
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.selectFn_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.selectFn_ite

@[expose] public section

namespace Domain.Recursive

/-- `halfParity n = pair (n / 2) (n % 2)`, built by structural recursion: from `(h, p)` for `n`, the
value for `n+1` is `(h + p, 1 - p)` (carry on odd→even). -/
def halfParity (n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun _ ih => Nat.pair (ih.unpair.1 + ih.unpair.2) (1 - ih.unpair.2)) n

end Domain.Recursive

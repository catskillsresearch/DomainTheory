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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.isOne_one
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.isOne_zero

@[expose] public section

namespace Domain.Recursive

set_option maxHeartbeats 800000 in

/-- `foldCode`-shaped indexing step. State `pair counter result`, parameter the target index `i`;
bump the counter and overwrite the result exactly when `counter = i` (via the `{0,1}` equality bit
`1 - ((counter - i) + (i - counter))`). -/
def nthStp (w : ℕ) : ℕ :=
  Nat.pair (w.unpair.2.unpair.1.unpair.1 + 1)
    (selectFn (1 - ((w.unpair.2.unpair.1.unpair.1 - w.unpair.2.unpair.2)
        + (w.unpair.2.unpair.2 - w.unpair.2.unpair.1.unpair.1)))
      w.unpair.1 w.unpair.2.unpair.1.unpair.2)

end Domain.Recursive

/-ai
The tabulation step reads a packed state whose first component pairs a length B with a parameter p, and whose second component pairs a counter y with a previous code. It returns one plus the pair of the value of g at B minus 1 minus y with p, and the previous code, thus prepending that value to the tail.
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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.isOne_one
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.isOne_zero

@[expose] public section

namespace Domain.Recursive

set_option maxHeartbeats 800000 in

/-- `tabCode`'s recursion step, in the `Nat.Primrec.prec` packaging: the state is
`pair a (pair y IH)` with `a = pair B p`; it prepends `g⟨B-1-y, p⟩` onto the tail `IH`. -/
def tabStep (g : ℕ → ℕ) (w : ℕ) : ℕ :=
  Nat.pair (g (Nat.pair (w.unpair.1.unpair.1 - 1 - w.unpair.2.unpair.1) w.unpair.1.unpair.2))
    w.unpair.2.unpair.2 + 1

end Domain.Recursive

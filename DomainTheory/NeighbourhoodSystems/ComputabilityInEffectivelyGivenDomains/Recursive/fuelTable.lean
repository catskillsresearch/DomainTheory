/-ai
The fuel table of a body lookup, a bound, and a fuel is the coded list of values, at every code from 0 through the bound, of the recursion with value 0 at fuel 0 and with that lookup as its step. Fuel 0 tabulates the zero function for one more entry than the bound, and each later fuel applies one fuel-table step to the previous table.
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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.tabCode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.fuelTableStep

@[expose] public section

namespace Domain.Recursive

set_option maxHeartbeats 800000 in

/-- Tabulates the fuel-recursive function with base value `0` and step `bodyLookup` at every code
in `[0, bound]`, as a coded list, for `fuel` iterations. -/
def fuelTable (bodyLookup : ℕ → ℕ) (bound fuel : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (tabCode (fun _ => 0) (Nat.pair (bound + 1) 0) (bound + 1))
    (fun _ prevTable => fuelTableStep bodyLookup bound prevTable) fuel

end Domain.Recursive

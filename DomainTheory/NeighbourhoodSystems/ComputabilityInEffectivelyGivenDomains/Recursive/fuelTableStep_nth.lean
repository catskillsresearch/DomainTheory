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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.Basic

@[expose] public section


namespace Domain.Recursive












































































































































































theorem fuelTableStep_nth {bodyLookup : ℕ → ℕ} {bound prevTable i : ℕ} (hi : i ≤ bound) (d : ℕ) :
    nthCode (fuelTableStep bodyLookup bound prevTable) i d = bodyLookup (Nat.pair prevTable i) := by
  unfold fuelTableStep
  rw [tabCode_nth_lt (show i < bound + 1 by omega)]
  simp only [unpair_pair_fst, unpair_pair_snd]

end Domain.Recursive

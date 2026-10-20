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





















































































































































































theorem selectFn_isOne_one_sub_sigma (u : ℕ) :
    selectFn (isOne (1 - u)) 1 0 = 1 ↔ u = 0 := by
  constructor
  · intro h
    by_cases hu : u = 0
    · exact hu
    · have : isOne (1 - u) = 0 := isOne_of_ne_one (by omega)
      simp [this, selectFn_zero] at h
  · intro hu
    subst hu
    simp [isOne_one, selectFn_one]

end Domain.Recursive

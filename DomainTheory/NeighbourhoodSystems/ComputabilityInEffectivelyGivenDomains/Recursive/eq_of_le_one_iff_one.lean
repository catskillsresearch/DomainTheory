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







































































































/-- Two `{0,1}`-bounded naturals agreeing on "`= 1`" are equal. -/
theorem eq_of_le_one_iff_one {x y : ℕ} (hx : x ≤ 1) (hy : y ≤ 1) (h : x = 1 ↔ y = 1) : x = y := by
  by_cases hx1 : x = 1
  · have hy1 := h.mp hx1; omega
  · have hy1 : y ≠ 1 := fun hy1 => hx1 (h.mpr hy1)
    omega

end Domain.Recursive

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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.sqrt_le
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.lt_succ_sqrt

@[expose] public section

set_option linter.unusedSectionVars false

namespace Domain.Recursive

/-- **The square-root characterization (choice-free).** If `q² ≤ m < (q+1)²` then `sqrt m = q`. The
uniqueness step is `omega` from the two bounds plus `sqrt_le`/`lt_succ_sqrt`. -/
theorem sqrt_eq_of {m q : ℕ} (h1 : q * q ≤ m) (h2 : m < (q + 1) * (q + 1)) : Nat.sqrt m = q := by
  have hle := sqrt_le m
  have hlt := lt_succ_sqrt m
  have hq_le : q ≤ Nat.sqrt m := by
    rcases Nat.lt_or_ge (Nat.sqrt m) q with hh | hh
    · exfalso
      have ha : Nat.sqrt m + 1 ≤ q := hh
      have hmul : (Nat.sqrt m + 1) * (Nat.sqrt m + 1) ≤ q * q := Nat.mul_le_mul ha ha
      omega
    · exact hh
  have hle_q : Nat.sqrt m ≤ q := by
    rcases Nat.lt_or_ge q (Nat.sqrt m) with hh | hh
    · exfalso
      have ha : q + 1 ≤ Nat.sqrt m := hh
      have hmul : (q + 1) * (q + 1) ≤ Nat.sqrt m * Nat.sqrt m := Nat.mul_le_mul ha ha
      omega
    · exact hh
  omega

end Domain.Recursive

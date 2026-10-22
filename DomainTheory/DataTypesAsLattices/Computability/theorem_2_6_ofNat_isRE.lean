/-ai
If the numeral of n is combinatory, then that numeral is recursively enumerable, the recursively enumerable direction of Theorem 2.6 for numerals.

The recursive enumerability of the numeral is IsRE.numeral n, which discharges the implication.
ai-/
module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.IsREu2enumeral

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Theorem 2.6, r.e. direction for numerals.** -/
theorem theorem_2_6_ofNat_isRE (n : ℕ) : IsCombinatory (ofNat n) → IsRE (ofNat n) :=
  fun _ => IsRE.numeral n

end DomainTheory.DataTypesAsLattices

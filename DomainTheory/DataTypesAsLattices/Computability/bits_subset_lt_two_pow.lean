module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Computability.lt_two_pow_of_high_bits

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem bits_subset_lt_two_pow {n b : ℕ} (h : e n ⊆ e b) : n < 2 ^ (b + 1) :=
  lt_two_pow_of_high_bits fun _j hj =>
    Bool.eq_false_iff.2 fun hbit =>
      Nat.not_le.mpr hj (mem_e_le (h (mem_e.mpr hbit)))

end DomainTheory.DataTypesAsLattices

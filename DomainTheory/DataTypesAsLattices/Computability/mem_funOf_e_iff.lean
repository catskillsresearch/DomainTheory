/-ai
A number m lies in the application of the finite set coded by a to the finite set coded by b if and only if some n < 2^(b + 1) has its finite set contained in the finite set coded by b and has bit pair(n, m) of a set.

An application witness n is contained in the finite set coded by b, hence lies below 2^(b + 1), and the paired code lies in the finite set coded by a. Conversely, such an n and bit are an application witness.
ai-/
module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.bits_subset_lt_two_pow

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem mem_funOf_e_iff (a b m : ℕ) :
    m ∈ funOf (e a) (e b) ↔
      ∃ n < 2 ^ (b + 1), e n ⊆ e b ∧ a.testBit (pair n m) := by
  constructor
  · intro ⟨n, hn, hp⟩
    exact ⟨n, bits_subset_lt_two_pow hn, hn, mem_e.mp hp⟩
  · intro ⟨n, _, hn, hbit⟩
    exact ⟨n, hn, mem_e.mpr hbit⟩

end DomainTheory.DataTypesAsLattices

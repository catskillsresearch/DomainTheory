module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Pomega.eDense
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
    exact ⟨n, bits_subset_lt_two_pow hn, hn, e.mem.mp hp⟩
  · intro ⟨n, _, hn, hbit⟩
    exact ⟨n, hn, e.mem.mpr hbit⟩

end DomainTheory.DataTypesAsLattices

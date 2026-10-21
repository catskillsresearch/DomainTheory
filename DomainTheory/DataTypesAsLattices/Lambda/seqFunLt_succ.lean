/-ai
The conditional that returns the functional at the numeral zero on a zero test, and otherwise the strict stage of the shifted functional at the predecessor, equals the strict stage of the functional at the next bound.

A left-branch member is the contribution of index zero below the successor bound. A right-branch member is an index below the old bound in the shifted application, which is the successor index in the unshifted stage. Conversely, index zero is the left branch and a successor index is the right branch after the shift equation for numerals.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.seqShift_ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.mem_seqFunLt

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem seqFunLt_succ (u z : Pomega) (n : ℕ) :
    condSet z (funOf u (ofNat 0)) (seqFunLt (seqShift u) (predSet z) n) =
      seqFunLt u z (n + 1) := by
  ext k
  constructor
  · intro hk
    rcases hk with ⟨hk0, h0z⟩ | ⟨hpos, t, ht⟩
    · exact (mem_seqFunLt).mpr ⟨0, h0z, Nat.succ_pos n, hk0⟩
    · obtain ⟨i, hi, hlt, hki⟩ := (mem_seqFunLt).mp hpos
      refine (mem_seqFunLt).mpr ⟨i + 1, hi, Nat.succ_lt_succ hlt, ?_⟩
      simpa [seqShift_ofNat] using hki
  · intro hk
    obtain ⟨i, hi, hlt, hki⟩ := (mem_seqFunLt).mp hk
    cases i with
    | zero => exact Or.inl ⟨hki, hi⟩
    | succ i =>
      refine Or.inr ⟨?_, i, hi⟩
      refine (mem_seqFunLt).mpr ⟨i, hi, Nat.lt_of_succ_lt_succ hlt, ?_⟩
      simpa [seqShift_ofNat] using hki

end DomainTheory.DataTypesAsLattices

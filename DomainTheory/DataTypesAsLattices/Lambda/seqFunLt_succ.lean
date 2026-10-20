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

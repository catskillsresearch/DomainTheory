/-ai
Revaluation of a functional along a set is the union over all bounds of the strict stages.

A value at an index in the set lies in the stage whose bound is one more than that index. Conversely, a value in some stage lies at an index in the set, and therefore in the revaluation.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.mem_seqFunLt

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem seqFun_eq_iUnion_lt (u z : Pomega) :
    seqFun u z = ⋃ n, seqFunLt u z n := by
  ext k
  constructor
  · intro hk
    obtain ⟨i, hi, hki⟩ := Set.mem_iUnion₂.mp hk
    exact Set.mem_iUnion.mpr ⟨i + 1, (mem_seqFunLt).mpr ⟨i, hi, Nat.lt_succ_self i, hki⟩⟩
  · intro hk
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hk
    obtain ⟨i, hi, _, hki⟩ := (mem_seqFunLt).mp hn
    exact Set.mem_iUnion₂.mpr ⟨i, hi, hki⟩

end DomainTheory.DataTypesAsLattices

module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices







































theorem seqFun_right_isScottContinuous (u : Pomega) :
    IsScottContinuous (fun x => seqFun u x) := by
  intro x
  ext k
  constructor
  · intro hk
    obtain ⟨i, hi, hki⟩ := Set.mem_iUnion₂.mp hk
    exact mem_scottUnion.mpr ⟨2 ^ i, by simp [e_pow2, Set.singleton_subset_iff, hi],
      Set.mem_iUnion₂.mpr ⟨i, by simp [e_pow2], hki⟩⟩
  · intro hk
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp hk
    obtain ⟨i, hi, hki⟩ := Set.mem_iUnion₂.mp hkn
    exact Set.mem_iUnion₂.mpr ⟨i, hn hi, hki⟩

end DomainTheory.DataTypesAsLattices

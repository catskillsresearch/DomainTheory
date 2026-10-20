module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices









theorem condSet_isScottContinuous_right (z x : Pomega) :
    IsScottContinuous (fun y => condSet z x y) := by
  intro y
  ext k
  constructor
  · intro hk
    rcases hk with hzx | ⟨hky, ht⟩
    · refine mem_scottUnion.mpr ⟨0, by simp [e_zero], Or.inl hzx⟩
    · refine mem_scottUnion.mpr ⟨2 ^ k, by simp [e_pow2, Set.singleton_subset_iff, hky],
        Or.inr ⟨by simp [e_pow2], ht⟩⟩
  · intro hk
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp hk
    rcases hkm with hzx | ⟨hky, ht⟩
    · exact Or.inl hzx
    · exact Or.inr ⟨hm hky, ht⟩

end DomainTheory.DataTypesAsLattices

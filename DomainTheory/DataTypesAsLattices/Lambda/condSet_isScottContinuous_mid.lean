module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices









theorem condSet_isScottContinuous_mid (z y : Pomega) :
    IsScottContinuous (fun x => condSet z x y) := by
  intro x
  ext k
  constructor
  · intro hk
    rcases hk with ⟨hkx, h0⟩ | hky
    · refine mem_scottUnion.mpr ⟨2 ^ k, by simp [e_pow2, Set.singleton_subset_iff, hkx],
        Or.inl ⟨by simp [e_pow2], h0⟩⟩
    · refine mem_scottUnion.mpr ⟨0, by simp [e_zero], Or.inr hky⟩
  · intro hk
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp hk
    rcases hkm with ⟨hkx, h0⟩ | hky
    · exact Or.inl ⟨hm hkx, h0⟩
    · exact Or.inr hky

end DomainTheory.DataTypesAsLattices

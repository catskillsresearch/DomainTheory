module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices









theorem id_isScottContinuous : IsScottContinuous (fun x : Pomega => x) := by
  intro x
  ext k
  constructor
  · intro hk
    exact mem_scottUnion.mpr ⟨2 ^ k, by simp [e_pow2, Set.singleton_subset_iff, hk],
      by simp [e_pow2]⟩
  · intro hk
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp hk
    exact hn hkn

end DomainTheory.DataTypesAsLattices

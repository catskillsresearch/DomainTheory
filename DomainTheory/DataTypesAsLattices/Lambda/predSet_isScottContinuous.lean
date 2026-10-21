/-ai
The predecessor operation is Scott continuous.

If k + 1 belongs to a set, the singleton finite set of k + 1 is contained in the set and its predecessor contains k, so k lies in the Scott union. Conversely, a Scott-union witness is a finite set contained in the original set whose predecessor already contains k.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem predSet_isScottContinuous : IsScottContinuous predSet := by
  intro x
  ext k
  constructor
  · intro hk
    refine mem_scottUnion.mpr ⟨2 ^ (k + 1), ?_, ?_⟩
    · simpa [e_pow2, Set.singleton_subset_iff, predSet] using hk
    · simp [predSet, e_pow2]
  · intro hk
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp hk
    exact hm hkm

end DomainTheory.DataTypesAsLattices

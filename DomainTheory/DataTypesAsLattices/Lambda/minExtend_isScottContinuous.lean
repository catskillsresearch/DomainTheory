/-ai
The minimal extension of any sequence of sets is Scott continuous.

If a number lies in the extension of a set, it lies in the value of the sequence at some index belonging to the set, and the singleton finite set of that index is a Scott-union witness. Conversely, a Scott-union witness contains some index at which the sequence value contains the number, and that index belongs to the original set.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem minExtend_isScottContinuous (p : ℕ → Pomega) :
    IsScottContinuous (minExtend p) := by
  intro x
  ext k
  constructor
  · intro hk
    obtain ⟨n, hn, hkn⟩ := Set.mem_iUnion₂.mp hk
    exact mem_scottUnion.mpr ⟨2 ^ n, by simp [e_pow2, Set.singleton_subset_iff, hn],
      by simp [minExtend, e_pow2, hkn]⟩
  · intro hk
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp hk
    obtain ⟨n, hn, hkn⟩ := Set.mem_iUnion₂.mp hkm
    exact Set.mem_iUnion₂.mpr ⟨n, hm hn, hkn⟩

end DomainTheory.DataTypesAsLattices

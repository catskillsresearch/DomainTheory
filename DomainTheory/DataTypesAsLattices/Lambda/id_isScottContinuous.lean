/-ai
The identity function on Pω is Scott continuous.

If a number lies in a set, the singleton finite set of that number is contained in the set and contains the number, so the number lies in the Scott union. Conversely, a Scott-union witness is a finite set contained in the original set that already contains the number.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem id_isScottContinuous : IsScottContinuous (fun x : Pomega => x) := by
  constructor
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

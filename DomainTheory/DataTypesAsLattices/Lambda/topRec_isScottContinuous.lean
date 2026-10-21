/-ai
The top recursion step is Scott continuous.

Fix x and a natural number k. If k belongs to the numeral 0, the code 0 has empty finite set contained in x and k lies in that piece of the step. If k is the successor of some n in x, then 2^n codes a singleton contained in x and k lies in the successor of that singleton. Conversely, membership in the Scott union supplies a finite piece contained in x and a disjunct of the step on that piece: either k belongs to the numeral 0, or k is the successor of a witness that still lies in x.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem topRec_isScottContinuous : IsScottContinuous topRec := by
  intro x
  ext k
  constructor
  · intro hk
    rcases hk with hk | ⟨n, hn, rfl⟩
    · exact mem_scottUnion.mpr ⟨0, by simp [e_zero], Or.inl hk⟩
    · exact mem_scottUnion.mpr ⟨2 ^ n, by simp [e_pow2, Set.singleton_subset_iff, hn],
        Or.inr ⟨n, by simp [e_pow2], rfl⟩⟩
  · intro hk
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp hk
    rcases hkm with hk | ⟨n, hn, rfl⟩
    · exact Or.inl hk
    · exact Or.inr ⟨n, hm hn, rfl⟩

end DomainTheory.DataTypesAsLattices

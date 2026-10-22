/-ai
For fixed x and y, the McCarthy conditional is Scott continuous in z.

Fix z and compare membership of a number k. If k lies in x and 0 lies in z, the basic element coded by 1 witnesses membership in the Scott union, since that element is contained in z and contains 0. If k lies in y and some successor t + 1 lies in z, the basic element coded by the power of two at t + 1 is the witness. Conversely, a member of the Scott union lies in the conditional at some basic element contained in z, so the witness that 0 or t + 1 belongs to that element still belongs to z.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.e_one

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem condSet_isScottContinuous_left (x y : Pomega) :
    IsScottContinuous (fun z => condSet z x y) := by
  constructor
  intro z
  ext k
  constructor
  · intro hk
    rcases hk with ⟨hkx, h0⟩ | ⟨hky, ⟨t, ht⟩⟩
    · refine mem_scottUnion.mpr ⟨1, ?_, Or.inl ⟨hkx, ?_⟩⟩
      · simp [e_one, Set.singleton_subset_iff, h0]
      · simp [e_one]
    · refine mem_scottUnion.mpr ⟨2 ^ (t + 1), ?_, Or.inr ⟨hky, t, ?_⟩⟩
      · simp [e_pow2, Set.singleton_subset_iff, ht]
      · simp [e_pow2]
  · intro hk
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp hk
    rcases hkm with ⟨hkx, h0⟩ | ⟨hky, ⟨t, ht⟩⟩
    · exact Or.inl ⟨hkx, hm h0⟩
    · exact Or.inr ⟨hky, t, hm ht⟩

end DomainTheory.DataTypesAsLattices

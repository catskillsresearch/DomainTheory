module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem funOf_isScottContinuous_left (y : Pomega) :
    IsScottContinuous (fun u => funOf u y) := by
  constructor
  intro u
  ext m
  constructor
  · intro ⟨n, hn, hp⟩
    refine mem_scottUnion.mpr ⟨2 ^ pair n m, ?_, ⟨n, hn, ?_⟩⟩
    · simp [e_pow2, Set.singleton_subset_iff, hp]
    · simp [e_pow2]
  · intro hm
    obtain ⟨k, hk, n, hn, hp⟩ := mem_scottUnion.mp hm
    exact ⟨n, hn, hk hp⟩

end DomainTheory.DataTypesAsLattices

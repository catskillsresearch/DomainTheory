/-ai
Application is Scott continuous in the function argument.

If a value is witnessed by an index and a pair code belonging to the function, the singleton finite set of that code is contained in the function and is a Scott-union witness carrying the same index. Conversely, the finite set of a Scott-union witness is contained in the function, so the pair code it carries belongs to the function.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem funOf_isScottContinuous_left (y : Pomega) :
    IsScottContinuous (fun u => funOf u y) := by
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

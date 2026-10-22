module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem funOf_iUnion (xs : ℕ → Pomega) (x : Pomega) :
    funOf (⋃ n, xs n) x = ⋃ n, funOf (xs n) x := by
  ext m
  constructor
  · intro ⟨n, hn, hk⟩
    obtain ⟨k, hmem⟩ := Set.mem_iUnion.mp hk
    exact Set.mem_iUnion.mpr ⟨k, ⟨n, hn, hmem⟩⟩
  · intro hm
    obtain ⟨k, ⟨n, hn, hmem⟩⟩ := Set.mem_iUnion.mp hm
    exact ⟨n, hn, Set.mem_iUnion.mpr ⟨k, hmem⟩⟩

end DomainTheory.DataTypesAsLattices

/-ai
Scott 1976, (2.13). Application distributes over an arbitrary union.

An element of the application of the union is witnessed by a finite set contained in the argument and a pair code in some member of the family, hence lies in the application of that member. A witness in the application of some member is a witness in the application of the union.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (2.13).** Application distributes over arbitrary unions. -/
theorem eq_2_13 (F : Set Pomega) (x : Pomega) :
    funOf (⋃₀ F) x = ⋃ u ∈ F, funOf u x := by
  ext m
  constructor
  · intro ⟨n, hn, hp⟩
    obtain ⟨u, hu, hpu⟩ := Set.mem_sUnion.mp hp
    exact Set.mem_iUnion₂.mpr ⟨u, hu, n, hn, hpu⟩
  · intro hm
    obtain ⟨u, hu, n, hn, hp⟩ := Set.mem_iUnion₂.mp hm
    exact ⟨n, hn, ⟨u, hu, hp⟩⟩

end DomainTheory.DataTypesAsLattices

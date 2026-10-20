module

public import DomainTheory.DataTypesAsLattices.Continuous
public import DomainTheory.DataTypesAsLattices.Graph.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices




theorem funOf_isScottContinuous (u : Pomega) : IsScottContinuous (funOf u) := by
  intro x
  ext m
  constructor
  · intro ⟨n, hn, hp⟩
    exact mem_scottUnion.mpr ⟨n, hn, ⟨n, subset_rfl, hp⟩⟩
  · intro hm
    obtain ⟨n, hn, ⟨k, hk, hp⟩⟩ := mem_scottUnion.mp hm
    exact ⟨k, subset_trans hk hn, hp⟩

end DomainTheory.DataTypesAsLattices

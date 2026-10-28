module

public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import Mathlib.Data.Set.Lattice.Indexed

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

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

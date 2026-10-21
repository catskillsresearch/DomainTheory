/-ai
If u is contained in v, then the application of u at x is contained in the application of v at x.

A witnessing code and pair for membership in the application of u remain a witness for v, because the pair lies in v.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Continuous
public import DomainTheory.DataTypesAsLattices.Graph.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem funOf_monotone_left {u v : Pomega} (h : u ⊆ v) (x : Pomega) :
    funOf u x ⊆ funOf v x := by
  intro m hm
  obtain ⟨n, hn, hp⟩ := hm
  exact ⟨n, hn, h hp⟩

end DomainTheory.DataTypesAsLattices

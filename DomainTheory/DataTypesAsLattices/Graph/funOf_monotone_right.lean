
module

public import DomainTheory.DataTypesAsLattices.Continuous
public import DomainTheory.DataTypesAsLattices.Graph.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem funOf_monotone_right (u : Pomega) {x y : Pomega} (h : x ⊆ y) :
    funOf u x ⊆ funOf u y := by
  intro m hm
  obtain ⟨n, hn, hp⟩ := hm
  exact ⟨n, subset_trans hn h, hp⟩

end DomainTheory.DataTypesAsLattices

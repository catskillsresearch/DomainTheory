module

public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Graph.IsGraph
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Pomega.pair

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem eq_2_11 (f g x : Pomega) :
    funOf (f ∩ g) x ⊆ funOf f x ∩ funOf g x := by
  intro m ⟨n, hn, hp, hq⟩
  exact ⟨⟨n, hn, hp⟩, ⟨n, hn, hq⟩⟩

namespace eq_2_11

theorem graphs {f g : Pomega} (hf : IsGraph f) (hg : IsGraph g)
    (x : Pomega) : funOf (f ∩ g) x = funOf f x ∩ funOf g x := by
  apply subset_antisymm (_root_.DomainTheory.DataTypesAsLattices.eq_2_11 f g x)
  intro m ⟨hf', hg'⟩
  obtain ⟨k, hk, hfk⟩ := hf'
  obtain ⟨l, hl, hgl⟩ := hg'
  refine ⟨k ||| l, e_or_of_subset hk hl, ⟨?_, ?_⟩⟩
  · exact hf.out hfk (by rw [e_or]; exact Set.subset_union_left)
  · exact hg.out hgl (by rw [e_or]; exact Set.subset_union_right)

end eq_2_11

end DomainTheory.DataTypesAsLattices

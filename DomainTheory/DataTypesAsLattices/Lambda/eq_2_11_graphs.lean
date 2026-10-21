/-ai
Scott 1976, (2.11). When both arguments are graphs, application preserves binary intersection.

One inclusion is the general inclusion for application of an intersection. Conversely, finite witnesses for the two applications may be joined by bitwise or. The joined finite set is still contained in the argument, and each graph remains closed when its finite argument is enlarged to that join.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.eq_2_11

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (2.11).** Equality when both arguments are graphs. -/
theorem eq_2_11_graphs {f g : Pomega} (hf : IsGraph f) (hg : IsGraph g)
    (x : Pomega) : funOf (f ∩ g) x = funOf f x ∩ funOf g x := by
  apply subset_antisymm (eq_2_11 f g x)
  intro m ⟨hf', hg'⟩
  obtain ⟨k, hk, hfk⟩ := hf'
  obtain ⟨l, hl, hgl⟩ := hg'
  refine ⟨k ||| l, e_or_of_subset hk hl, ⟨?_, ?_⟩⟩
  · exact hf hfk (by rw [e_or]; exact Set.subset_union_left)
  · exact hg hgl (by rw [e_or]; exact Set.subset_union_right)

end DomainTheory.DataTypesAsLattices

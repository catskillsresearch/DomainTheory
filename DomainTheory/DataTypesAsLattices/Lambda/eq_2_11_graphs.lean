/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

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

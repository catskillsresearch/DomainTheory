/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices









/-- `graph (fun y => g x y)` is continuous in `x` when `g` is continuous in `x`. -/
theorem graph_const_isScottContinuous
    (g : Pomega → Pomega → Pomega)
    (hg : ∀ y, IsScottContinuous (fun x => g x y)) :
    IsScottContinuous (fun x => graph (fun y => g x y)) := by
  intro x
  ext k
  constructor
  · intro hk
    rcases hk with ⟨n, m, rfl, hm⟩
    have : m ∈ scottUnion (fun z => g z (e n)) x := by
      rw [← hg (e n) x]; exact hm
    obtain ⟨p, hp, hmp⟩ := mem_scottUnion.mp this
    exact mem_scottUnion.mpr ⟨p, hp, n, m, rfl, hmp⟩
  · intro hk
    obtain ⟨p, hp, n, m, rfl, hm⟩ := mem_scottUnion.mp hk
    exact ⟨n, m, rfl, isScottContinuous_monotone (hg (e n)) hp hm⟩

end DomainTheory.DataTypesAsLattices

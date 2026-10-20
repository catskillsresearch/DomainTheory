/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Continuous
import DomainTheory.DataTypesAsLattices.Graph.Basic


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

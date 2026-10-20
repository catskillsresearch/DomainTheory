/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.funOf_iUnion
import DomainTheory.DataTypesAsLattices.Lambda.seqFun_eq_iUnion_lt
import DomainTheory.DataTypesAsLattices.Lambda.termDollarStep_iterate


namespace DomainTheory.DataTypesAsLattices






















































theorem termDollarStep_fix_app (u z : Pomega) :
    funOf (funOf (fix termDollarStep) u) z = seqFun u z := by
  have : funOf (funOf (fix termDollarStep) u) z =
      ⋃ n, funOf (funOf (iterateBot termDollarStep n) u) z := by
    simp [fix, funOf_iUnion]
  rw [this, seqFun_eq_iUnion_lt]
  ext k
  constructor
  · intro hk
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hk
    exact Set.mem_iUnion.mpr ⟨n, by simpa [termDollarStep_iterate] using hn⟩
  · intro hk
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hk
    exact Set.mem_iUnion.mpr ⟨n, by simpa [termDollarStep_iterate] using hn⟩

end DomainTheory.DataTypesAsLattices

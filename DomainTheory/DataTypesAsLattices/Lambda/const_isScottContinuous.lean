/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic


namespace DomainTheory.DataTypesAsLattices









theorem const_isScottContinuous (c : Pomega) :
    IsScottContinuous (fun _ : Pomega => c) := by
  intro x
  ext k
  constructor
  · intro hk
    exact mem_scottUnion.mpr ⟨0, by simp [e_zero], hk⟩
  · intro hk
    obtain ⟨_, _, hkn⟩ := mem_scottUnion.mp hk
    exact hkn

end DomainTheory.DataTypesAsLattices

/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.funOf_isScottContinuous_left


namespace DomainTheory.DataTypesAsLattices









theorem diagApp_isScottContinuous : IsScottContinuous (fun x => funOf x x) := by
  intro x
  have h := theorem_1_3_diag (x := x)
    (f := fun u y => funOf u y)
    (fun y => funOf_isScottContinuous_left y)
    (fun u => funOf_isScottContinuous u)
  ext k
  constructor
  · intro hk
    have : k ∈ ⋃ n, {k | e n ⊆ x ∧ k ∈ funOf (e n) (e n)} := by rwa [← h]
    obtain ⟨n, hn, hkn⟩ := Set.mem_iUnion.mp this
    exact mem_scottUnion.mpr ⟨n, hn, hkn⟩
  · intro hk
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp hk
    have : k ∈ ⋃ n, {k | e n ⊆ x ∧ k ∈ funOf (e n) (e n)} :=
      Set.mem_iUnion.mpr ⟨n, hn, hkn⟩
    rwa [← h] at this

end DomainTheory.DataTypesAsLattices

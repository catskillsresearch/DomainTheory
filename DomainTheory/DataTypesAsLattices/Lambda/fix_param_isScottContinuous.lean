/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.iterateBot_param_isScottContinuous


namespace DomainTheory.DataTypesAsLattices















































theorem fix_param_isScottContinuous
    {g : Pomega → Pomega → Pomega}
    (hgx : ∀ y, IsScottContinuous (fun x => g x y))
    (hgy : ∀ x, IsScottContinuous (fun y => g x y)) :
    IsScottContinuous (fun x => fix (g x)) := by
  intro x
  ext k
  constructor
  · intro hk
    obtain ⟨n, hkn⟩ := Set.mem_iUnion.mp hk
    have := iterateBot_param_isScottContinuous hgx hgy n x
    have : k ∈ scottUnion (fun z => iterateBot (g z) n) x := by
      rwa [← this]
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp this
    exact mem_scottUnion.mpr ⟨m, hm, Set.mem_iUnion.mpr ⟨n, hkm⟩⟩
  · intro hk
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp hk
    obtain ⟨n, hkn⟩ := Set.mem_iUnion.mp hkm
    exact Set.mem_iUnion.mpr ⟨n,
      isScottContinuous_monotone (iterateBot_param_isScottContinuous hgx hgy n) hm hkn⟩

end DomainTheory.DataTypesAsLattices

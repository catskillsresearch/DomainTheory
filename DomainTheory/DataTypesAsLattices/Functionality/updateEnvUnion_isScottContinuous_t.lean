/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.updateEnv_isScottContinuous_t

@[expose] public section


namespace DomainTheory.DataTypesAsLattices






































theorem updateEnvUnion_isScottContinuous_t (x idx : Pomega) :
    IsScottContinuous (fun t => updateEnvUnion t x idx) := by
  intro t
  ext k
  constructor
  · intro hk
    obtain ⟨n, hn, hkn⟩ := Set.mem_iUnion₂.mp hk
    have : k ∈ scottUnion (fun t => updateEnv t x n) t := by
      rw [← updateEnv_isScottContinuous_t x n t]; exact hkn
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp this
    exact mem_scottUnion.mpr ⟨m, hm, Set.mem_iUnion₂.mpr ⟨n, hn, hkm⟩⟩
  · intro hk
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp hk
    obtain ⟨n, hn, hkn⟩ := Set.mem_iUnion₂.mp hkm
    exact Set.mem_iUnion₂.mpr ⟨n, hn,
      isScottContinuous_monotone (updateEnv_isScottContinuous_t x n) hm hkn⟩

end DomainTheory.DataTypesAsLattices

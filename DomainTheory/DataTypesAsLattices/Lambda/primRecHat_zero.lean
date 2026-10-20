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















































theorem primRecHat_zero (a f : Pomega) : primRecHat a f (ofNat 0) = a := by
  ext k
  constructor
  · intro hk
    obtain ⟨n, hn, hkn⟩ := Set.mem_iUnion₂.mp hk
    simp [ofNat] at hn; subst hn; simpa [primRecVal] using hkn
  · intro hk
    exact Set.mem_iUnion₂.mpr ⟨0, rfl, hk⟩

end DomainTheory.DataTypesAsLattices

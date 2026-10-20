/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.primRecHat_zero


namespace DomainTheory.DataTypesAsLattices















































/-- **Scott 1976, (2.27).** The distributive extension agrees with the
integer recursion on singletons. -/
theorem primRecHat_ofNat (a f : Pomega) : ∀ n,
    primRecHat a f (ofNat n) = primRecVal a f n
  | 0 => primRecHat_zero a f
  | n + 1 => by
    ext k
    constructor
    · intro hk
      obtain ⟨m, hm, hkm⟩ := Set.mem_iUnion₂.mp hk
      simp [ofNat] at hm; subst hm; simpa [primRecVal] using hkm
    · intro hk
      exact Set.mem_iUnion₂.mpr ⟨n + 1, rfl, hk⟩

end DomainTheory.DataTypesAsLattices

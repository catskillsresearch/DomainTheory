/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Computability.RE
import DomainTheory.DataTypesAsLattices.Lambda
import DomainTheory.DataTypesAsLattices.Computability.Basic


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code



attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4







































theorem enumRangeC_eq {r : Pomega} {p : ℕ → ℕ} (hr : Realizes r p) :
    enumRangeC r = ⋃ n, ofNat (p n) := by
  rw [enumRangeC, eq_2_25]
  ext k
  constructor
  · intro hk
    obtain ⟨n, _, hkn⟩ := Set.mem_iUnion₂.mp hk
    exact Set.mem_iUnion.mpr ⟨n, by simpa [hr n] using hkn⟩
  · intro hk
    obtain ⟨n, hkn⟩ := Set.mem_iUnion.mp hk
    exact Set.mem_iUnion₂.mpr ⟨n, Set.mem_univ n, by simpa [hr n] using hkn⟩

end DomainTheory.DataTypesAsLattices

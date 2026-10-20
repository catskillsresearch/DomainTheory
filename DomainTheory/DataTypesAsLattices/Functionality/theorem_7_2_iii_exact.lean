/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.theorem_4_4_typed


namespace DomainTheory.DataTypesAsLattices






















/-- **Scott 1976, Theorem 7.2 (iii).**
The printed identity `E_{a ⊗ b} = E_a × E_b`, for arbitrary representatives. -/
theorem theorem_7_2_iii_exact (a b u v : Pomega) :
    (Ea (tensorR a b)).rel u v ↔ (prodE (Ea a) (Ea b)).rel u v := by
  constructor
  · intro huv
    rcases huv with ⟨hu, hv, rfl⟩
    rcases (theorem_4_4_typed.mp hu) with ⟨hpair, ha, hb⟩
    refine ⟨hpair, hpair, ?_, ?_⟩
    · exact ⟨ha, ha, rfl⟩
    · exact ⟨hb, hb, rfl⟩
  · intro huv
    rcases huv with ⟨hu, hv, h0, h1⟩
    rcases h0 with ⟨hx, hx', heqx⟩
    rcases h1 with ⟨hy, hy', heqy⟩
    have huvEq : u = v := by
      rw [hu, hv, heqx, heqy]
    refine ⟨?_, ?_, huvEq⟩
    · exact theorem_4_4_typed.mpr ⟨hu, hx, hy⟩
    · exact theorem_4_4_typed.mpr ⟨hv, hx', hy'⟩

end DomainTheory.DataTypesAsLattices

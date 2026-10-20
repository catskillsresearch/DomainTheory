/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem eSubset_iff_stage {x : Pomega} {c : Code}
    (hc : Code.eval c = fun k => Part.assert (k ∈ x) fun _ => Part.some (0 : ℕ))
    (n : ℕ) :
    e n ⊆ x ↔ ∃ s, ∀ k < n, n.testBit k = false ∨ (evaln s c k).isSome = true := by
  constructor
  · intro hsub
    let stage : ℕ → ℕ := fun k =>
      if h : n.testBit k = true then
        ((evaln_complete (x := 0)).1 (by
          rw [hc]
          exact Part.mem_assert_iff.mpr ⟨hsub (mem_e.mpr h), Part.mem_some_iff.mpr rfl⟩)).choose
      else 0
    refine ⟨(Finset.range n).sup stage, fun k hlt => ?_⟩
    by_cases hb : n.testBit k = true
    · refine Or.inr ?_
      have hle : stage k ≤ (Finset.range n).sup stage :=
        Finset.le_sup (Finset.mem_range.mpr hlt)
      have h0 : 0 ∈ evaln (stage k) c k := by
        simp only [stage, hb, ↓reduceDIte]
        exact ((evaln_complete (x := 0)).1 (by
          rw [hc]
          exact Part.mem_assert_iff.mpr ⟨hsub (mem_e.mpr hb), Part.mem_some_iff.mpr rfl⟩)).choose_spec
      exact (Option.isSome_of_mem (evaln_mono hle h0))
    · exact Or.inl (Bool.eq_false_iff.mpr hb)
  · intro ⟨s, hs⟩ k hk
    have hlt : k < n := mem_e_lt hk
    have hsome : (evaln s c k).isSome = true :=
      (hs k hlt).resolve_left fun hfalse => Bool.eq_false_iff.mp hfalse (mem_e.mp hk)
    obtain ⟨val, hval⟩ := Option.isSome_iff_exists.mp hsome
    have : val ∈ Code.eval c k :=
      evaln_sound (by simpa [Option.mem_def] using hval)
    have : val ∈ (Part.assert (k ∈ x) fun _ => Part.some (0 : ℕ)) := by
      simpa [hc] using this
    exact (Part.mem_assert_iff.mp this).1

end DomainTheory.DataTypesAsLattices

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
public import DomainTheory.DataTypesAsLattices.Computability.IsREu2epredSet
public import DomainTheory.DataTypesAsLattices.Computability.IsREu2epredC
public import DomainTheory.DataTypesAsLattices.Computability.primrec_realized
public import DomainTheory.DataTypesAsLattices.Computability.primrec_enumFun
public import DomainTheory.DataTypesAsLattices.Computability.enumRangeC_combinatory
public import DomainTheory.DataTypesAsLattices.Computability.enumRangeC_eq

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code



attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4







































/-- **Scott 1976, Appendix.** Every r.e. element belongs to the
combinatory closure. -/
theorem IsRE.combinatory {u : Pomega} (hu : IsRE u) : IsCombinatory u := by
  have hpart : Partrec fun k : ℕ =>
      Part.assert (k ∈ u) fun _ => Part.some (0 : ℕ) :=
    hu.map (Computable.const (0 : ℕ)).to₂
  obtain ⟨c, hc⟩ := Code.exists_code.1 (Partrec.nat_iff.1 hpart)
  obtain ⟨r, hr, hreal⟩ := primrec_realized (primrec_enumFun c)
  have hrange := enumRangeC_eq hreal
  have hpred : DataTypesAsLattices.predSet (enumRangeC r) = u := by
    ext n
    constructor
    · intro hn
      rw [hrange] at hn
      obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hn
      have heq : enumFun c t = n + 1 := by simpa [ofNat] using ht.symm
      have hs : (evaln t.unpair.2 c t.unpair.1).isSome = true := by
        by_contra h
        have : (evaln t.unpair.2 c t.unpair.1).isSome = false :=
          Bool.eq_false_of_not_eq_true h
        simp [enumFun, this] at heq
      have hfirst : t.unpair.1 = n := by
        simp [enumFun, hs] at heq
        omega
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
      have hmem : v ∈ Code.eval c t.unpair.1 :=
        evaln_sound (by simpa [Option.mem_def] using hv)
      rw [hc] at hmem
      simpa [hfirst] using (Part.mem_assert_iff.mp hmem).1
    · intro hn
      have hmem : 0 ∈ Code.eval c n := by
        rw [hc]
        exact Part.mem_assert_iff.mpr ⟨hn, Part.mem_some_iff.mpr rfl⟩
      obtain ⟨s, hs⟩ := evaln_complete.mp hmem
      rw [hrange]
      refine Set.mem_iUnion.mpr ⟨Nat.pair n s, ?_⟩
      have hsome : (evaln s c n).isSome = true := Option.isSome_of_mem hs
      simp [enumFun, Nat.unpair_pair, hsome, ofNat]
  have hcomb : IsCombinatory (DataTypesAsLattices.predC ⬝ enumRangeC r) :=
    .app .pred (enumRangeC_combinatory hr)
  rw [DataTypesAsLattices.predC_app, hpred] at hcomb
  exact hcomb

end DomainTheory.DataTypesAsLattices

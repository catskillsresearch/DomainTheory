/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Computability.RE
import DomainTheory.DataTypesAsLattices.Lambda
import DomainTheory.DataTypesAsLattices.Computability.Basic
import DomainTheory.DataTypesAsLattices.Computability.REPredu2ecomp
import DomainTheory.DataTypesAsLattices.Computability.REPredu2eand
import DomainTheory.DataTypesAsLattices.Computability.primrec_pair
import DomainTheory.DataTypesAsLattices.Computability.primrecRel_mem_funOf_e
import DomainTheory.DataTypesAsLattices.Computability.eSubset_funOf_e_iff
import DomainTheory.DataTypesAsLattices.Computability.primrec_pack4_proj1
import DomainTheory.DataTypesAsLattices.Computability.primrec_pack4_proj3
import DomainTheory.DataTypesAsLattices.Computability.primrec_pack4_proj4
import DomainTheory.DataTypesAsLattices.Computability.primrecPred_Scomb_subset


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code



attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4

theorem primrecRel_Scomb_app :
    PrimrecRel fun k t : ℕ =>
      e k ⊆ e (pack4_proj2 t) ⬝ e (pack4_proj3 t) ∧
        pair k (pack4_proj4 t) ∈ e (pack4_proj1 t) ⬝ e (pack4_proj3 t) := by
  have hmem : PrimrecPred fun p : ℕ × ℕ =>
      pair p.1 (pack4_proj4 p.2) ∈
        e (pack4_proj1 p.2) ⬝ e (pack4_proj3 p.2) :=
    (primrecRel_mem_funOf_e.comp
      (Primrec₂.natPair.comp (primrec_pack4_proj1.comp Primrec.snd)
        (primrec_pack4_proj3.comp Primrec.snd))
      (primrec_pair.comp Primrec.fst (primrec_pack4_proj4.comp Primrec.snd))).of_eq
      fun p => by simp [Nat.unpair_pair]
  refine (primrecPred_Scomb_subset.and hmem).of_eq fun p => ?_
  constructor
  · intro ⟨hs, hm⟩
    exact ⟨(eSubset_funOf_e_iff _ _ _).mpr hs, hm⟩
  · intro ⟨hs, hm⟩
    exact ⟨(eSubset_funOf_e_iff _ _ _).mp hs, hm⟩

end DomainTheory.DataTypesAsLattices

/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Computability.Halting
import DomainTheory.DataTypesAsLattices.Computability
import DomainTheory.DataTypesAsLattices.Functionality
import DomainTheory.DataTypesAsLattices.Enumeration.Basic
import DomainTheory.DataTypesAsLattices.Enumeration.filterRealizer_realizes
import DomainTheory.DataTypesAsLattices.Enumeration.filterSeq_isScottContinuous


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code



























theorem filterC_app (m : ℕ) :
    funOf filterC (ofNat m) = {j | ∀ i ≤ j, haltEnum i ≠ m} := by
  have hgraph :
      filterC = graph (fun v =>
        predSet (seqFun
          (graph (fun j =>
            funOf filterRealizer (funOf (funOf pairComb v) j)))
          topElem)) := by
    unfold filterC filterTerm
    apply congrArg graph
    funext v
    simp [interp, envSet, Function.update, filterEnv, eq_2_25]
  have hcont : IsScottContinuous fun v =>
      predSet (seqFun
        (graph (fun j => funOf filterRealizer (funOf (funOf pairComb v) j)))
        topElem) :=
    theorem_1_3 predSet_isScottContinuous
      (theorem_1_3 (seqFun_left_isScottContinuous topElem)
        filterSeq_isScottContinuous)
  have hbody :
      funOf filterC (ofNat m) =
        predSet (seqFun
          (graph (fun j =>
            funOf filterRealizer (funOf (funOf pairComb (ofNat m)) j)))
          topElem) := by
    rw [hgraph]
    exact beta hcont (ofNat m)
  have hseq (i : ℕ) :
      funOf (graph (fun j =>
          funOf filterRealizer (funOf (funOf pairComb (ofNat m)) j)))
        (ofNat i) =
        ofNat (filterNum (Nat.pair m i)) := by
    have hβ : funOf (graph (fun j =>
        funOf filterRealizer (funOf (funOf pairComb (ofNat m)) j)))
        (ofNat i) =
        funOf filterRealizer (funOf (funOf pairComb (ofNat m)) (ofNat i)) :=
      beta (theorem_1_3 (funOf_isScottContinuous filterRealizer)
        (funOf_isScottContinuous (funOf pairComb (ofNat m)))) (ofNat i)
    rw [hβ, pairComb_app, filterRealizer_realizes]
  rw [hbody]
  ext j
  constructor
  · intro hj
    have : j + 1 ∈ seqFun
        (graph (fun z =>
          funOf filterRealizer (funOf (funOf pairComb (ofNat m)) z)))
        topElem := hj
    obtain ⟨i, -, hij⟩ := Set.mem_iUnion₂.mp this
    have : filterNum (Nat.pair m i) = j + 1 := by
      have hij' : j + 1 ∈ ofNat (filterNum (Nat.pair m i)) := by
        rwa [← hseq i]
      simpa [ofNat, eq_comm] using hij'
    have hbf : beforeHalt m i := by
      by_contra h
      simp [filterNum, Nat.unpair_pair, h] at this
    have hij' : i = j := by
      simp [filterNum, Nat.unpair_pair, hbf] at this
      omega
    subst hij'
    simpa [beforeHalt, Nat.lt_succ_iff] using hbf
  · intro hj
    have hbf : beforeHalt m j := by
      simpa [beforeHalt, Nat.lt_succ_iff] using hj
    have : filterNum (Nat.pair m j) = j + 1 := by
      simp [filterNum, Nat.unpair_pair, hbf]
    refine (show j + 1 ∈ seqFun
        (graph (fun z =>
          funOf filterRealizer (funOf (funOf pairComb (ofNat m)) z)))
        topElem from ?_)
    refine Set.mem_iUnion₂.mpr ⟨j, Set.mem_univ j, ?_⟩
    have : j + 1 ∈ ofNat (filterNum (Nat.pair m j)) := by
      simp [ofNat, this]
    rwa [← hseq j] at this

end DomainTheory.DataTypesAsLattices

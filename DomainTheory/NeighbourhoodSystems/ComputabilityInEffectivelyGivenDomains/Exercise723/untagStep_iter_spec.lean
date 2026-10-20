/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.unnum1_spec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.unnum2_spec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.untagRef_zero_case
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.untagRef_succ_case
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.untagStep_of_done_iterate
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.untagStep_halt
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.untagStep_cont

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)






























































/-- **Main invariant.** Given enough fuel (`c ≤ fuel`), `fuel + 1` iterations of `untagStep` from a
fresh `code = c` state (arbitrary carried `r`, `v`) freeze with `revAcc` holding `(untagRef c).1`
consed onto `r` (i.e. `reverse (untagRef c).1 ++ decodeList r`, matching `appendCode`'s convention)
and `val` holding `(untagRef c).2`. -/
theorem untagStep_iter_spec : ∀ c, ∀ fuel r v : ℕ, c ≤ fuel →
    untagStep^[fuel + 1] (Nat.pair c (Nat.pair 0 (Nat.pair r v))) =
      Nat.pair (untagRef c).2 (Nat.pair 1
        (Nat.pair ((untagRef c).1.foldl (fun acc x => Nat.pair x acc + 1) r) (untagRef c).2)) := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro fuel r v hfuel
    set w : ℕ := Nat.pair c (Nat.pair 0 (Nat.pair r v)) with hw
    have hw1 : w.unpair.1 = c := by rw [hw, unpair_pair_fst]
    have hw2 : w.unpair.2.unpair.1 = 0 := by rw [hw]; simp only [unpair_pair_snd, unpair_pair_fst]
    have hw3 : w.unpair.2.unpair.2.unpair.1 = r := by
      rw [hw]; simp only [unpair_pair_snd, unpair_pair_fst]
    have hw4 : w.unpair.2.unpair.2.unpair.2 = v := by
      rw [hw]; simp only [unpair_pair_snd]
    rw [Function.iterate_succ_apply]
    rcases hc : (unnum c).1 with _ | k
    · have ha0 : unnum1 w.unpair.1 = 0 := by rw [hw1, unnum1_spec, hc]
      have hstep : untagStep w = Nat.pair (unnum c).2 (Nat.pair 1 (Nat.pair r (unnum c).2)) := by
        rw [untagStep_halt hw2 ha0, hw1, hw3, unnum2_spec]
      rw [hstep]
      have hdone1 : (Nat.pair (unnum c).2
          (Nat.pair 1 (Nat.pair r (unnum c).2))).unpair.2.unpair.1 = 1 := by
        simp only [unpair_pair_snd, unpair_pair_fst]
      rw [untagStep_of_done_iterate _ hdone1, untagRef_zero_case hc, List.foldl_nil]
    · have hak : unnum1 w.unpair.1 = k + 1 := by rw [hw1, unnum1_spec, hc]
      set b : ℕ := (unnum c).2 with hbdef
      have hblt : b < c := unnum_snd_lt_of_fst_succ hc
      have hc1 : 1 ≤ c := by omega
      have hstep : untagStep w = Nat.pair b (Nat.pair 0 (Nat.pair (Nat.pair k r + 1) v)) := by
        rw [untagStep_cont hw2 hak, hw1, hw3, hw4, unnum2_spec]
      rw [hstep]
      rcases fuel with _ | fuel'
      · omega
      · have hble : b ≤ fuel' := by omega
        have hihb := ih b hblt fuel' (Nat.pair k r + 1) v hble
        rw [hihb]
        have href := untagRef_succ_case (c := c) (k := k) hc
        rw [← hbdef] at href
        rw [href, List.foldl_cons]

end DomainTheory.NeighbourhoodSystems.Exercise723

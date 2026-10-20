/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Exercise823
public import DomainTheory.Neighborhood.Exercise824.Basic
public import DomainTheory.Neighborhood.Exercise824.fst_mono
public import DomainTheory.Neighborhood.Exercise824.snd_mono
public import DomainTheory.Neighborhood.Exercise824.isFinitaryProjection_chain

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Sub8_6 Exercise823

namespace Exercise824

variable {α : Type} {E : NeighborhoodSystem α}












/-- **Exercise 8.24, Claim 1.** Provided `s`/`t` map pairs of finitary projections to finitary
projections, the simultaneous fixed point `(aStar s t, bStar s t)` really consists of finitary
projections. -/
theorem isFinitaryProjection_aStar_bStar (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E))
    (hst : ∀ a b, IsFinitaryProjection a → IsFinitaryProjection b →
      IsFinitaryProjection (binOp s a b) ∧ IsFinitaryProjection (binOp t a b)) :
    IsFinitaryProjection (aStar s t) ∧ IsFinitaryProjection (bStar s t) := by
  have hchain := isFinitaryProjection_chain s t hst
  have hsubA : ∀ n, subFilter (((paired s t).iterElem n).fst) = ((paired s t).iterElem n).fst := by
    intro n
    apply toApproxMap_injective
    rw [toApproxMap_subFilter]
    show sub (aOp s t n) = aOp s t n
    exact sub_eq_self_of_isFinitaryProjection (hchain n).1
  have hsubB : ∀ n, subFilter (((paired s t).iterElem n).snd) = ((paired s t).iterElem n).snd := by
    intro n
    apply toApproxMap_injective
    rw [toApproxMap_subFilter]
    show sub (bOp s t n) = bOp s t n
    exact sub_eq_self_of_isFinitaryProjection (hchain n).2
  have hdirA : ∀ i j : ℕ, ∃ k, ((paired s t).iterElem i).fst ≤ ((paired s t).iterElem k).fst ∧
      ((paired s t).iterElem j).fst ≤ ((paired s t).iterElem k).fst :=
    fun i j => ⟨max i j, fst_mono (iterElem_mono (paired s t) (le_max_left i j)),
      fst_mono (iterElem_mono (paired s t) (le_max_right i j))⟩
  have hdirB : ∀ i j : ℕ, ∃ k, ((paired s t).iterElem i).snd ≤ ((paired s t).iterElem k).snd ∧
      ((paired s t).iterElem j).snd ≤ ((paired s t).iterElem k).snd :=
    fun i j => ⟨max i j, snd_mono (iterElem_mono (paired s t) (le_max_left i j)),
      snd_mono (iterElem_mono (paired s t) (le_max_right i j))⟩
  have hdirSubA : ∀ i j : ℕ, ∃ k, subFilter (((paired s t).iterElem i).fst) ≤
      subFilter (((paired s t).iterElem k).fst) ∧
      subFilter (((paired s t).iterElem j).fst) ≤ subFilter (((paired s t).iterElem k).fst) := by
    intro i j
    obtain ⟨k, hik, hjk⟩ := hdirA i j
    exact ⟨k, by rw [hsubA i, hsubA k]; exact hik, by rw [hsubA j, hsubA k]; exact hjk⟩
  have hdirSubB : ∀ i j : ℕ, ∃ k, subFilter (((paired s t).iterElem i).snd) ≤
      subFilter (((paired s t).iterElem k).snd) ∧
      subFilter (((paired s t).iterElem j).snd) ≤ subFilter (((paired s t).iterElem k).snd) := by
    intro i j
    obtain ⟨k, hik, hjk⟩ := hdirB i j
    exact ⟨k, by rw [hsubB i, hsubB k]; exact hik, by rw [hsubB j, hsubB k]; exact hjk⟩
  have hEqA : (paired s t).fixElement.fst =
      iSupDirected (fun n => ((paired s t).iterElem n).fst) hdirA := by
    apply Element.ext
    intro X
    rw [mem_fst, mem_fixElement, mem_iSupDirected]
    constructor
    · rintro ⟨hX, n, hn⟩
      exact ⟨n, mem_fst.mpr ⟨hX, (mem_iterElem (paired s t) n).mpr hn⟩⟩
    · rintro ⟨n, hn⟩
      rw [mem_fst] at hn
      exact ⟨hn.1, n, (mem_iterElem (paired s t) n).mp hn.2⟩
  have hEqB : (paired s t).fixElement.snd =
      iSupDirected (fun n => ((paired s t).iterElem n).snd) hdirB := by
    apply Element.ext
    intro X
    rw [mem_snd, mem_fixElement, mem_iSupDirected]
    constructor
    · rintro ⟨hX, n, hn⟩
      exact ⟨n, mem_snd.mpr ⟨hX, (mem_iterElem (paired s t) n).mpr hn⟩⟩
    · rintro ⟨n, hn⟩
      rw [mem_snd] at hn
      exact ⟨hn.1, n, (mem_iterElem (paired s t) n).mp hn.2⟩
  have hkeyA : subFilter ((paired s t).fixElement.fst) = (paired s t).fixElement.fst := by
    rw [hEqA, subFilter_iSupDirected _ hdirA hdirSubA]
    apply Element.ext
    intro Z
    rw [mem_iSupDirected, mem_iSupDirected]
    simp_rw [hsubA]
  have hkeyB : subFilter ((paired s t).fixElement.snd) = (paired s t).fixElement.snd := by
    rw [hEqB, subFilter_iSupDirected _ hdirB hdirSubB]
    apply Element.ext
    intro Z
    rw [mem_iSupDirected, mem_iSupDirected]
    simp_rw [hsubB]
  refine ⟨?_, ?_⟩
  · show IsFinitaryProjection (toApproxMap (paired s t).fixElement.fst)
    apply isFinitaryProjection_of_sub_eq_self
    rw [← toApproxMap_subFilter, hkeyA]
  · show IsFinitaryProjection (toApproxMap (paired s t).fixElement.snd)
    apply isFinitaryProjection_of_sub_eq_self
    rw [← toApproxMap_subFilter, hkeyB]

end Exercise824
end DomainTheory.Neighborhood

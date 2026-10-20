/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Cat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Words
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.PathSplit
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.instFintypeAutState
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.instDecidableEqAutState
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.pathStateAt_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.accepts_skip_loop

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability

open Sum Set

variable {σ₁ σ₂ : Type}

variable {σ : Type}

section ShortWord

variable {σ : Type} [Fintype σ] {M : NFA Bool σ}

theorem accepts_shorten_step {x : List Bool} (hx : x ∈ M.accepts)
    (hlen : Fintype.card σ ≤ x.length) :
    ∃ y, y ∈ M.accepts ∧ y.length < x.length := by
  rw [NFA.accepts_iff_exists_path] at hx
  obtain ⟨s, hs, t, ht, ⟨hp⟩⟩ := hx
  obtain ⟨i, j, hne, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt
      (f := fun k : Fin (x.length + 1) => pathStateAt hp k.val (Nat.le_of_lt_succ k.isLt))
      (by rw [Fintype.card_fin]; exact Nat.lt_succ_iff.mpr hlen)
  have hval : i.val ≠ j.val := fun h => hne (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hval with hij | hij
  · refine ⟨x.take i.val ++ x.drop j.val, ?_, ?_⟩
    · exact accepts_skip_loop (by omega) (by omega) hij hs ht hp heq
    · have : j.val - i.val > 0 := Nat.sub_pos_of_lt hij
      simp [List.length_append, List.length_take, List.length_drop]
      omega
  · refine ⟨x.take j.val ++ x.drop i.val, ?_, ?_⟩
    · exact accepts_skip_loop (by omega) (by omega) hij hs ht hp heq.symm
    · have : i.val - j.val > 0 := Nat.sub_pos_of_lt hij
      simp [List.length_append, List.length_take, List.length_drop]
      omega

end ShortWord

end Exercise722

end DomainTheory.NeighbourhoodSystems

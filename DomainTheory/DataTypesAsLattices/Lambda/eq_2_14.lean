/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.id_isScottContinuous
import DomainTheory.DataTypesAsLattices.Lambda.omega_first_recursion


namespace DomainTheory.DataTypesAsLattices




























/-- **Scott 1976, (2.14).** `⊥ = (λx. x(x))(λx. x(x))`. -/
theorem eq_2_14 :
    funOf (graph (fun x => funOf x x)) (graph (fun x => funOf x x)) = botElem := by
  have hω : omegaComb (graph fun x => x) = graph (fun x => funOf x x) := by
    ext p
    constructor
    · intro hp
      rcases hp with ⟨n, m, rfl, hm⟩
      rw [theorem_1_2_i id_isScottContinuous] at hm
      exact ⟨n, m, rfl, hm⟩
    · intro hp
      rcases hp with ⟨n, m, rfl, hm⟩
      refine ⟨n, m, rfl, ?_⟩
      rw [theorem_1_2_i id_isScottContinuous]
      exact hm
  rw [← hω, omega_first_recursion id_isScottContinuous]
  apply subset_antisymm
  · intro k hk
    obtain ⟨n, hkn⟩ := Set.mem_iUnion.mp hk
    have : ∀ n, iterateBot (fun x => x) n = botElem := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => simp [iterateBot, ih]
    simp [this n] at hkn
  · intro k hk
    exact hk.elim


end DomainTheory.DataTypesAsLattices

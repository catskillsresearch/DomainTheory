/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.FunctionSpace
import DomainTheory.Neighborhood.Definition72
import DomainTheory.Neighborhood.Theorem74
import DomainTheory.Neighborhood.Theorem75.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}










variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)









































































































/-- **The step neighbourhood `[X₀ⱼ, Y₁ₘ]` as a one-entry `Xenum`.** The code `⟨⟨j, m⟩, 0⟩ + 1`
decodes to the singleton entry-list `[⟨j, m⟩]`, which is always consistent (the step map itself is a
witness), so `Xenum` of it is `stepFun [(X₀ⱼ, Y₁ₘ)] = [X₀ⱼ, Y₁ₘ]`. -/
theorem Xenum_singleton (gN : ℕ → ℕ)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf P₀ P₁ (decodeList c))
      : Set (ApproximableMap V₀ V₁)).Nonempty) (j m : ℕ) :
    Xenum P₀ P₁ gN (Nat.pair (Nat.pair j m) 0 + 1) = step (P₀.X j) (P₁.X m) := by
  have hfp : funPair P₀ P₁ (Nat.pair j m) = (P₀.X j, P₁.X m) := by
    show (P₀.X (Nat.pair j m).unpair.1, P₁.X (Nat.pair j m).unpair.2) = (P₀.X j, P₁.X m)
    rw [unpair_pair_fst, unpair_pair_snd]
  have hdec : decodeList (Nat.pair (Nat.pair j m) 0 + 1) = [Nat.pair j m] := by
    rw [decodeList_succ, unpair_pair_fst, unpair_pair_snd, decodeList_zero]
  have hstepeq : (stepFun (funListOf P₀ P₁ [Nat.pair j m]) : Set (ApproximableMap V₀ V₁))
      = step (P₀.X j) (P₁.X m) := by
    show stepFun [funPair P₀ P₁ (Nat.pair j m)] = step (P₀.X j) (P₁.X m)
    rw [hfp, stepFun_singleton]
  have hcons : gN (Nat.pair (Nat.pair j m) 0 + 1) = 1 := by
    rw [hgN, hdec, hstepeq]; exact (step_mem (P₀.mem_X j) (P₁.mem_X m)).2
  rw [Xenum_pos P₀ P₁ hcons, hdec, hstepeq]

end DomainTheory.Neighborhood

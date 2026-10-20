/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise424.sbSet
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise424.sbFun
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise424.sbFun_mem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise424.g_sbFun_not_mem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise424.g_f_mem_of_mem

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise424

open DomainTheory.NeighbourhoodSystems.Exercise414 Function

variable {A B : Type*} {f : A → B} {g : B → A}

theorem sbFun_injective (hf : Injective f) : Injective (sbFun f g) := by
  intro a₁ a₂ heq
  by_cases h1 : a₁ ∈ sbSet f g <;> by_cases h2 : a₂ ∈ sbSet f g
  · rw [sbFun_mem h1, sbFun_mem h2] at heq
    exact hf heq
  · -- `a₁ ∈ X`, `a₂ ∉ X`: `f a₁ = g⁻¹ a₂` ⟹ `a₂ = g(f a₁) ∈ X`, contradiction.
    exfalso
    rw [sbFun_mem h1] at heq
    have : a₂ = g (f a₁) := by rw [heq, g_sbFun_not_mem h2]
    exact h2 (this ▸ g_f_mem_of_mem h1)
  · exfalso
    rw [sbFun_mem h2] at heq
    have : a₁ = g (f a₂) := by rw [← heq, g_sbFun_not_mem h1]
    exact h1 (this ▸ g_f_mem_of_mem h2)
  · -- both off `X`: apply `g` and use injectivity of `g`.
    have : g (sbFun f g a₁) = g (sbFun f g a₂) := by rw [heq]
    rw [g_sbFun_not_mem h1, g_sbFun_not_mem h2] at this
    exact this

end DomainTheory.NeighbourhoodSystems.Exercise424

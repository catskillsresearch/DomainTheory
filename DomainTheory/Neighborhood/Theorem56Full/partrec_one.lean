/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Example43
import DomainTheory.Neighborhood.Exercise326
import DomainTheory.Neighborhood.Exercise511
import DomainTheory.Neighborhood.Theorem41
import DomainTheory.Neighborhood.ApproximableExercises
import Mathlib.Computability.PartrecBasis
import DomainTheory.Neighborhood.Theorem56Full.Basic
import DomainTheory.Neighborhood.Theorem56Full.component_bot
import DomainTheory.Neighborhood.Theorem56Full.partrec_lamDef
import DomainTheory.Neighborhood.Theorem56Full.oneArg_natElem
import DomainTheory.Neighborhood.Theorem56Full.oneArg_bot


namespace DomainTheory.Neighborhood.Theorem56Full

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap
open DomainTheory.Neighborhood.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)
open DomainTheory.Neighborhood.Exercise326 (cond)
open DomainTheory.Neighborhood.Exercise511 (head tail push)




























/-- **Scott's 1-ary meta-theorem.** A partial recursive `h : ℕ →. ℕ` (presented as a unary
`Nat.Partrec'`) is denoted by a single approximable map `τ : N → N` that is correct on values,
divergent where `h` diverges, and strict. -/
theorem partrec_one {h : ℕ →. ℕ}
    (H : Nat.Partrec' (fun v : List.Vector ℕ 1 => h v.head)) :
    ∃ τ : ApproximableMap N N,
      (∀ a m, m ∈ h a → τ.toElementMap (natElem a) = natElem m) ∧
      (∀ a, ¬ (h a).Dom → τ.toElementMap (natElem a) = N.bot) ∧
      τ.toElementMap N.bot = N.bot := by
  obtain ⟨φ, hφ⟩ := partrec_lamDef H
  refine ⟨φ.comp oneArg, ?_, ?_, ?_⟩
  · intro a m hm
    rw [toElementMap_comp, oneArg_natElem]
    refine hφ.defined (a ::ᵥ List.Vector.nil) m ?_
    rwa [List.Vector.head_cons]
  · intro a hdom
    rw [toElementMap_comp, oneArg_natElem]
    refine hφ.undef (a ::ᵥ List.Vector.nil) ?_
    rwa [List.Vector.head_cons]
  · rw [toElementMap_comp, oneArg_bot]
    refine hφ.strict 𝒩.bot (fun j => Or.inl (component_bot j)) 0 (by omega) (component_bot 0)

end DomainTheory.Neighborhood.Theorem56Full

/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Example43
public import DomainTheory.Neighborhood.Exercise326
public import DomainTheory.Neighborhood.Exercise511
public import DomainTheory.Neighborhood.Theorem41
public import DomainTheory.Neighborhood.ApproximableExercises
public import Mathlib.Computability.PartrecBasis
import all Mathlib.Computability.PartrecBasis
public import DomainTheory.Neighborhood.Theorem56Full.Basic
public import DomainTheory.Neighborhood.Theorem56Full.component_bot
public import DomainTheory.Neighborhood.Theorem56Full.partrec_lamDef
public import DomainTheory.Neighborhood.Theorem56Full.oneArg_natElem
public import DomainTheory.Neighborhood.Theorem56Full.oneArg_bot

@[expose] public section


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

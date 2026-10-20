/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import Mathlib.Computability.PartrecBasis
import all Mathlib.Computability.PartrecBasis
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.lamDef_coe_val
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.push_natElem_vecElem
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.recMap_rec

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Theorem56Full

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)
open DomainTheory.NeighbourhoodSystems.Exercise511 (head tail push)





















section Prec

variable (φf φg : ApproximableMap 𝒩 N)




/-- **Primitive recursion computes.** `recMap(⟨d, u⟩) = (Nat.rec (f u) (g …) d)`. -/
theorem recMap_eval {n : ℕ} (f₀ : List.Vector ℕ n → ℕ) (g₀ : List.Vector ℕ (n + 2) → ℕ)
    (hf : LamDef φf (f₀ : List.Vector ℕ n →. ℕ)) (hg : LamDef φg (g₀ : List.Vector ℕ (n + 2) →. ℕ))
    (u : List.Vector ℕ n) (d : ℕ) :
    (recMap φf φg).toElementMap (vecElem (d ::ᵥ u))
      = natElem (Nat.rec (motive := fun _ => ℕ) (f₀ u)
          (fun y IH => g₀ (y ::ᵥ IH ::ᵥ u)) d) := by
  induction d with
  | zero =>
    rw [← push_natElem_vecElem, recMap_rec, Exercise511.head_push, Exercise511.tail_push,
      zeroMap_natElem_zero, Exercise326.cond_true]
    exact lamDef_coe_val hf u
  | succ d ih =>
    rw [← push_natElem_vecElem, recMap_rec, Exercise511.head_push, Exercise511.tail_push,
      zeroMap_natElem_succ, Exercise326.cond_false, predMap_natElem_succ, push_natElem_vecElem, ih,
      push_natElem_vecElem, push_natElem_vecElem]
    exact lamDef_coe_val hg _

end Prec
end DomainTheory.NeighbourhoodSystems.Theorem56Full

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

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Theorem56Full

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)
open DomainTheory.NeighbourhoodSystems.Exercise511 (head tail push)



















/-- Membership in `mOfFn` (Part monad): a vector is produced iff each coordinate is a value. -/
theorem mem_mOfFn : ∀ {n : ℕ} (p : Fin n → Part ℕ) (w : List.Vector ℕ n),
    w ∈ List.Vector.mOfFn p ↔ ∀ i, w.get i ∈ p i
  | 0, p, w => by
      constructor
      · intro _ i; exact i.elim0
      · intro _
        show w ∈ (pure List.Vector.nil : Part _)
        rw [Part.pure_eq_some, Part.mem_some_iff]
        exact List.Vector.eq_nil w
  | n + 1, p, w => by
      have hmof : List.Vector.mOfFn p
          = (p 0).bind (fun a => (List.Vector.mOfFn fun i => p i.succ).bind
              (fun u => Part.some (a ::ᵥ u))) := by
        simp only [List.Vector.mOfFn, Part.bind_eq_bind, Part.pure_eq_some]
      rw [hmof, Part.mem_bind_iff]
      constructor
      · rintro ⟨a, ha, hrest⟩
        rw [Part.mem_bind_iff] at hrest
        obtain ⟨u, hu, hw⟩ := hrest
        rw [Part.mem_some_iff] at hw
        subst hw
        have hu' := (mem_mOfFn (fun i => p i.succ) u).mp hu
        intro i
        refine Fin.cases ?_ ?_ i
        · simpa using ha
        · intro k; simpa using hu' k
      · intro hall
        refine ⟨w.head, ?_, ?_⟩
        · have := hall 0; rwa [List.Vector.get_zero] at this
        · rw [Part.mem_bind_iff]
          refine ⟨w.tail, (mem_mOfFn (fun i => p i.succ) w.tail).mpr (fun k => ?_), ?_⟩
          · have h := hall k.succ
            rwa [← List.Vector.get_tail_succ w k] at h
          · rw [Part.mem_some_iff]; exact (List.Vector.cons_head_tail w).symm

end DomainTheory.NeighbourhoodSystems.Theorem56Full

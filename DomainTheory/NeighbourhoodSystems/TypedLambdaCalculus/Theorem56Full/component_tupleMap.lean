/-ai
For each i below n, the i-th coordinate of the tuple of n scalar maps, evaluated at a stack, is the i-th map evaluated at that stack.

Induct on n. No index is below zero. For a successor, the zeroth coordinate is the head of the push of the zeroth map's value onto the remaining tuple, hence that value, up to agreement of the zero indices. A later coordinate is the corresponding coordinate of the tail, which the inductive hypothesis identifies with the shifted map, and the shifted index agrees with the original index.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import Mathlib.Computability.PartrecBasis
import all Mathlib.Computability.PartrecBasis
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.component_push_zero
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.component_push_succ
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.tupleMap_succ

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Theorem56Full

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)
open DomainTheory.NeighbourhoodSystems.Exercise511 (head tail push)


/-- Coordinate `i < n` of the tuple is exactly `gᵢ`. -/
theorem component_tupleMap : ∀ (n : ℕ) (gs : Fin n → ApproximableMap 𝒩 N) (z : 𝒩.Element)
    (i : ℕ) (hi : i < n),
    component ((tupleMap n gs).toElementMap z) i = (gs ⟨i, hi⟩).toElementMap z
  | 0, _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, gs, z, 0, hi => by
      rw [tupleMap_succ, toElementMap_comp, toElementMap_paired, component_push_zero]
      exact congrArg (fun w => (gs w).toElementMap z) (Fin.ext (by simp))
  | n + 1, gs, z, i + 1, hi => by
      rw [tupleMap_succ, toElementMap_comp, toElementMap_paired, component_push_succ,
        component_tupleMap n (fun j => gs j.succ) z i (Nat.lt_of_succ_lt_succ hi)]
      rfl

end DomainTheory.NeighbourhoodSystems.Theorem56Full

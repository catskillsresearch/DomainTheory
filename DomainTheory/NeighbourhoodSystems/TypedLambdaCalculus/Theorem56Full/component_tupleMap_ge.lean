module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import Mathlib.Computability.PartrecBasis
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.component_push_succ
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.tupleMap_succ
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.component_bot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.tupleMap_zero

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Theorem56Full

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)
open DomainTheory.NeighbourhoodSystems.Exercise511 (head tail push)


/-- Coordinates `≥ n` of the tuple are `⊥`. -/
theorem component_tupleMap_ge : ∀ (n : ℕ) (gs : Fin n → ApproximableMap 𝒩 N) (z : 𝒩.Element)
    (i : ℕ), n ≤ i → component ((tupleMap n gs).toElementMap z) i = N.bot
  | 0, gs, z, i, _ => by rw [tupleMap_zero, toElementMap_constMap, component_bot]
  | n + 1, gs, z, i, hi => by
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      rw [tupleMap_succ, toElementMap_comp, toElementMap_paired, component_push_succ]
      exact component_tupleMap_ge n (fun k => gs k.succ) z j (by omega)

end DomainTheory.NeighbourhoodSystems.Theorem56Full

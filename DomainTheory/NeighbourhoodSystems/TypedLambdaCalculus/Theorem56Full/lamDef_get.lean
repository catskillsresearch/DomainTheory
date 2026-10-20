module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import Mathlib.Computability.PartrecBasis
import all Mathlib.Computability.PartrecBasis
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.component_vecElem_lt
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.lamDef_total

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Theorem56Full

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)
open DomainTheory.NeighbourhoodSystems.Exercise511 (head tail push)


















/-- `get i : Vector ℕ n → ℕ`, the `i`-th projection. -/
theorem lamDef_get {n : ℕ} (i : Fin n) :
    LamDef (strictGuardN n (projN N i))
      ((fun v => v.get i : List.Vector ℕ n → ℕ) : List.Vector ℕ n →. ℕ) :=
  lamDef_total _ _ (fun v => by
    rw [toElementMap_projN, component_vecElem_lt v i.isLt, Fin.eta])

end DomainTheory.NeighbourhoodSystems.Theorem56Full

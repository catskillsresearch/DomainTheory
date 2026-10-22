module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import Mathlib.Computability.PartrecBasis
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.eq_of_component_eq
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.component_push_zero
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.component_push_succ
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.component_bot

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Theorem56Full

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)
open DomainTheory.NeighbourhoodSystems.Exercise511 (head tail push)


theorem oneArg_bot : (oneArg).toElementMap N.bot = 𝒩.bot := by
  rw [oneArg, toElementMap_comp, toElementMap_paired, toElementMap_idMap, toElementMap_constMap]
  apply eq_of_component_eq
  intro i
  cases i with
  | zero => rw [component_push_zero, component_bot]
  | succ k => rw [component_push_succ, component_bot, component_bot]

end DomainTheory.NeighbourhoodSystems.Theorem56Full

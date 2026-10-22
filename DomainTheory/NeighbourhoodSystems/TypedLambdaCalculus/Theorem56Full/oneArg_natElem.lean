module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import Mathlib.Computability.PartrecBasis
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.eq_of_component_eq
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.component_bot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.push_natElem_vecElem

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Theorem56Full

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)
open DomainTheory.NeighbourhoodSystems.Exercise511 (head tail push)


theorem oneArg_natElem (a : ℕ) :
    (oneArg).toElementMap (natElem a) = vecElem (a ::ᵥ (List.Vector.nil : List.Vector ℕ 0)) := by
  rw [oneArg, toElementMap_comp, toElementMap_paired, toElementMap_idMap, toElementMap_constMap]
  rw [show 𝒩.bot = vecElem (List.Vector.nil : List.Vector ℕ 0) from ?_, push_natElem_vecElem]
  exact eq_of_component_eq (fun i => by rw [component_bot, component_vecElem, dite_eq_right (by omega)])

end DomainTheory.NeighbourhoodSystems.Theorem56Full

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



















/-- A realiser of a total function evaluates to its value. -/
theorem lamDef_coe_val {n : ℕ} {φ : ApproximableMap 𝒩 N} {g : List.Vector ℕ n → ℕ}
    (h : LamDef φ (g : List.Vector ℕ n →. ℕ)) (v : List.Vector ℕ n) :
    φ.toElementMap (vecElem v) = natElem (g v) :=
  h.defined v (g v) (by rw [PFun.coe_val]; exact Part.mem_some _)

end DomainTheory.NeighbourhoodSystems.Theorem56Full

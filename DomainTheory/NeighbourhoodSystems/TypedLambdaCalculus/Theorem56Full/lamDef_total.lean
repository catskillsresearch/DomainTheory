module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import Mathlib.Computability.PartrecBasis
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.lamDef_of_inner

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Theorem56Full

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)
open DomainTheory.NeighbourhoodSystems.Exercise511 (head tail push)


/-- The total-function specialisation of `lamDef_of_inner`. -/
theorem lamDef_total {n : ℕ} (ψ : ApproximableMap 𝒩 N) (g : List.Vector ℕ n → ℕ)
    (hval : ∀ v, ψ.toElementMap (vecElem v) = natElem (g v)) :
    LamDef (strictGuardN n ψ) (g : List.Vector ℕ n →. ℕ) :=
  lamDef_of_inner ψ _
    (fun v c hc => by rw [PFun.coe_val, Part.mem_some_iff] at hc; rw [hval, ← hc])
    (fun v hv => by rw [PFun.coe_val] at hv; exact absurd trivial hv)

end DomainTheory.NeighbourhoodSystems.Theorem56Full

/-ai
The starting search at the stack of a vector equals the running search at the stack of the vector with 0 consed on.

Unfold the starting map and simplify the element maps of the two compositions, the pairing, the constant map, and the identity, then use that pushing a numeral onto a vector stack is the stack of the consed vector.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import Mathlib.Computability.PartrecBasis
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.push_natElem_vecElem

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Theorem56Full

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)
open DomainTheory.NeighbourhoodSystems.Exercise511 (head tail push)


section Rfind

variable (φf : ApproximableMap 𝒩 N)


theorem findMap_vecElem {n : ℕ} (v : List.Vector ℕ n) :
    (findMap φf).toElementMap (vecElem v) = (searchMap φf).toElementMap (vecElem (0 ::ᵥ v)) := by
  rw [findMap, toElementMap_comp, toElementMap_comp, toElementMap_paired, toElementMap_constMap,
    toElementMap_idMap, push_natElem_vecElem]

end Rfind
end DomainTheory.NeighbourhoodSystems.Theorem56Full

module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Theorem56

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN constLiftN_natElem)
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)



theorem strictId_natElem (n : ℕ) : strictId.toElementMap (natElem n) = natElem n := by
  rw [strictId, toElementMap_comp]
  simp only [toElementMap_paired, toElementMap_idMap]
  cases n with
  | zero => rw [zeroMap_natElem_zero, Exercise326.cond_true]
  | succ k => rw [zeroMap_natElem_succ, Exercise326.cond_false]

end DomainTheory.NeighbourhoodSystems.Theorem56

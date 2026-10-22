/-ai
The i-th component of the stack of a vector of length n is the numeral at position i when i lies below n, and bottom otherwise.

Unfold the vector element as an argument element and apply the component formula. Both branches of the bound test agree.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import Mathlib.Computability.PartrecBasis
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.LamDef
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.component_argElem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Theorem56Full

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)

open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)

open DomainTheory.NeighbourhoodSystems.Exercise511 (head tail push)

@[simp] theorem component_vecElem {n : ℕ} (v : List.Vector ℕ n) (i : ℕ) :
    component (vecElem v) i = if h : i < n then natElem (v.get ⟨i, h⟩) else N.bot := by
  rw [vecElem, component_argElem]; split <;> rfl

end DomainTheory.NeighbourhoodSystems.Theorem56Full

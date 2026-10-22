/-ai
Evaluation at a fixed stack is the approximable map on the function space that applies a function-space element to that stack. It is evaluation composed with the pairing of the identity and the constant map with that stack as its value.
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
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.component_vecElem

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

/-- `evalAt z` evaluates a function-space element at the fixed argument `z`. -/
def evalAt (z : 𝒩.Element) : ApproximableMap (funSpace 𝒩 N) N :=
  (evalMap 𝒩 N).comp (paired (idMap (funSpace 𝒩 N)) (constMap (funSpace 𝒩 N) z))

end Rfind

end DomainTheory.NeighbourhoodSystems.Theorem56Full

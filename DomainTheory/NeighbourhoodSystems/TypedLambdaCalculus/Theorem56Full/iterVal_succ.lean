/-ai
The value of the next approximant of the search at a stack unfolds one search step, using the previous approximant as the continuation. It is the conditional on the zero test of the function at the stack, the head, and the previous approximant applied to the push of the successor of that head onto the tail.

The next approximant is the search operator applied to the previous one, by writing approximants as iterates and using the successor law for iteration. Currying the body at the previous approximant and the stack, then rewriting by the definition of the operator and the application lemma for the body, gives the conditional.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import Mathlib.Computability.PartrecBasis
import all Mathlib.Computability.PartrecBasis
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.findBody_apply

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.iterElem_eq_iterate
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


/-- Recursion equation for the approximant values: `S^{m+1}(⊥)` unfolds one search step using
`Sᵐ(⊥)` as the continuation. -/
theorem iterVal_succ (m : ℕ) (z : 𝒩.Element) :
    (toApproxMap ((findOp φf).iterElem (m + 1))).toElementMap z =
      (cond N).toElementMap
        (pair (zeroMap.toElementMap (φf.toElementMap z))
          (pair ((head N).toElementMap z)
            ((toApproxMap ((findOp φf).iterElem m)).toElementMap
              ((push N).toElementMap
                (pair (succMap.toElementMap ((head N).toElementMap z))
                  ((tail N).toElementMap z)))))) := by
  have h1 : (findOp φf).iterElem (m + 1) = (findOp φf).toElementMap ((findOp φf).iterElem m) := by
    rw [iterElem_eq_iterate, iterElem_eq_iterate, Function.iterate_succ', Function.comp_apply]
  rw [h1]
  have hval := toElementMap_curry_apply (findBody φf) ((findOp φf).iterElem m) z
  rw [← findOp] at hval
  rw [hval, findBody_apply]

end Rfind
end DomainTheory.NeighbourhoodSystems.Theorem56Full

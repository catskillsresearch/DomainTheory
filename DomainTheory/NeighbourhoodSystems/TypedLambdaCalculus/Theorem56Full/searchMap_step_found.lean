/-ai
If f at the vector with head k and tail v equals zero, the search at the argument element of that vector returns the numeral for k.

Rewrite the argument as a push, apply the search equation, compute the head and tail of a push, restore the pushed numeral, use the value clause of the λ-definition together with the hypothesis that the value is zero, and take the true branch of the conditional on the zero-test of the numeral zero.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import Mathlib.Computability.PartrecBasis
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.lamDef_coe_val
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.push_natElem_vecElem
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.searchMap_rec

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


/-- **Search step (found).** If `f(k ::ᵥ v) = 0`, the search returns the counter `k`. -/
theorem searchMap_step_found {n : ℕ} {f : List.Vector ℕ (n + 1) → ℕ}
    (hf : LamDef φf (f : List.Vector ℕ (n + 1) →. ℕ)) (v : List.Vector ℕ n) (k : ℕ)
    (h0 : f (k ::ᵥ v) = 0) :
    (searchMap φf).toElementMap (vecElem (k ::ᵥ v)) = natElem k := by
  rw [← push_natElem_vecElem, searchMap_rec, Exercise511.head_push, Exercise511.tail_push,
    push_natElem_vecElem, lamDef_coe_val hf (k ::ᵥ v), h0, zeroMap_natElem_zero,
    Exercise326.cond_true]

end Rfind
end DomainTheory.NeighbourhoodSystems.Theorem56Full

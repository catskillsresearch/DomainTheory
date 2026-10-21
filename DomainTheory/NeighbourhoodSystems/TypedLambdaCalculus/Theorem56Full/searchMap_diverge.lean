/-ai
If f has no zero along the vectors with tail v, the search returns bottom from every counter.

Antisymmetry with the leastness of bottom reduces the claim to an inequality. Rewrite the search through evaluation at the argument, express the least fixed point as the directed supremum of its approximants, and push the element map through that supremum. Each approximant, evaluated at the argument element of the counter followed by v, equals bottom, so the supremum lies below bottom.
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
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.evalAt_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.iterVal_bot

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







/-- **Divergence.** If `f(· ::ᵥ v)` has no zero, the search is `⊥` from every counter. The fixed point
is the directed union of the approximants `Sᵐ(⊥)` (Theorem 4.2(iii)); pushing the evaluation at
`vecElem (k ::ᵥ v)` through this sup (continuity, `toElementMap_iSupDirected`) reduces the claim to
`iterVal_bot`. -/
theorem searchMap_diverge {n : ℕ} {f : List.Vector ℕ (n + 1) → ℕ}
    (hf : LamDef φf (f : List.Vector ℕ (n + 1) →. ℕ)) (v : List.Vector ℕ n)
    (hdiv : ∀ k, f (k ::ᵥ v) ≠ 0) (k : ℕ) :
    (searchMap φf).toElementMap (vecElem (k ::ᵥ v)) = N.bot := by
  refine le_antisymm ?_ (N.bot_le _)
  rw [searchMap, ← evalAt_apply, fixElement_eq_iSupDirected, toElementMap_iSupDirected]
  apply NeighborhoodSystem.iSupDirected_le
  intro m
  rw [evalAt_apply]
  exact le_of_eq (iterVal_bot φf hf v hdiv m k)

end Rfind
end DomainTheory.NeighbourhoodSystems.Theorem56Full

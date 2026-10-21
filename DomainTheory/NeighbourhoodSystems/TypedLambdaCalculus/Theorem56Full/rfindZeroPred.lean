/-ai
Given a total function f of one more argument than a vector v, the zero predicate sends each k to the boolean decision of whether f at k followed by v equals zero, packaged as a partial boolean so that unbounded search is well-typed without unfolding the partial-function abbreviation.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import Mathlib.Computability.PartrecBasis
import all Mathlib.Computability.PartrecBasis
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.LamDef
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.component_argElem
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.component_vecElem

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Theorem56Full

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)

open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)

open DomainTheory.NeighbourhoodSystems.Exercise511 (head tail push)

section Rfind

variable (φf : ApproximableMap 𝒩 N)

/-- The `ℕ →. Bool` predicate `k ↦ f(k ::ᵥ v) = 0`, packaged so `Nat.rfind` is well-typed at
implicit transparency (Lean 4.33: `ℕ →. Bool` no longer unfolds to `ℕ → Part Bool` in `rw`). -/
def rfindZeroPred {n : ℕ} (f : List.Vector ℕ (n + 1) → ℕ) (v : List.Vector ℕ n) : ℕ →. Bool :=
  fun k => Part.some (decide (f (k ::ᵥ v) = 0))

end Rfind

end DomainTheory.NeighbourhoodSystems.Theorem56Full

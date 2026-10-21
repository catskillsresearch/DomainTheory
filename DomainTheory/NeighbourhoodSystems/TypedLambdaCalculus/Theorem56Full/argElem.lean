/-ai
The argument element of a finite family of optional numerals is the stack whose coordinate i is the optional numeral at i when i lies below the length, and bottom otherwise.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import Mathlib.Computability.PartrecBasis
import all Mathlib.Computability.PartrecBasis
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.𝒩
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.optElem

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Theorem56Full

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)

open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)

open DomainTheory.NeighbourhoodSystems.Exercise511 (head tail push)

/-- The argument element of `𝒩` whose first `n` coordinates are `optElem (a i)` and the rest `⊥`. -/
def argElem {n : ℕ} (a : Fin n → Option ℕ) : 𝒩.Element :=
  ofSeq (fun i => if h : i < n then optElem (a ⟨i, h⟩) else N.bot)

end DomainTheory.NeighbourhoodSystems.Theorem56Full

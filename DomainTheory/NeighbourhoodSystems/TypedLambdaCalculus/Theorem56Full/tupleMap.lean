/-ai
The tuple of length n places a family of n approximable maps into successive coordinates of the universal argument domain, with bottom from coordinate n onward. Length 0 is the constant bottom map. Length n + 1 pushes the zeroth map in front of the tuple of the remaining maps.
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

/-- `⟨g₀, …, g_{n-1}⟩ : 𝒩 → 𝒩` placing `gᵢ` at coordinate `i` (`< n`) and `⊥` beyond. -/
def tupleMap : (n : ℕ) → (Fin n → ApproximableMap 𝒩 N) → ApproximableMap 𝒩 𝒩
  | 0, _ => constMap 𝒩 𝒩.bot
  | n + 1, gs => (push N).comp (paired (gs 0) (tupleMap n (fun i => gs i.succ)))

end DomainTheory.NeighbourhoodSystems.Theorem56Full

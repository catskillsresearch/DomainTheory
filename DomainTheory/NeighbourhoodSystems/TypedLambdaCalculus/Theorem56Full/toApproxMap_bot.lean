/-ai
The approximable map corresponding to the bottom element of the function space from the universal argument domain to N evaluates to bottom at every argument.

Antisymmetry with the leastness of bottom reduces the claim to an inequality. Monotonicity of the function-space equivalence, applied because bottom lies below the inverse image of the constant bottom map, and rewriting by the inverse law and the action of the equivalence, shows that the bottom map lies below the constant bottom map. Evaluating that inequality and rewriting the constant map gives bottom.
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


/-- The least map of the function space evaluates to `⊥` everywhere. -/
theorem toApproxMap_bot (z : 𝒩.Element) :
    (toApproxMap ((funSpace 𝒩 N).bot)).toElementMap z = N.bot := by
  refine le_antisymm ?_ (N.bot_le _)
  have h2 := (funSpaceEquiv 𝒩 N).monotone
    ((funSpace 𝒩 N).bot_le ((funSpaceEquiv 𝒩 N).symm (constMap 𝒩 N.bot)))
  rw [OrderIso.apply_symm_apply, funSpaceEquiv_apply] at h2
  have h3 := (le_iff_toElementMap_le.mp h2) z
  rwa [toElementMap_constMap] at h3

end Rfind
end DomainTheory.NeighbourhoodSystems.Theorem56Full

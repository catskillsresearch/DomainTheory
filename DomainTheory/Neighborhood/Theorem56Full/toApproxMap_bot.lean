/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Example43
import DomainTheory.Neighborhood.Exercise326
import DomainTheory.Neighborhood.Exercise511
import DomainTheory.Neighborhood.Theorem41
import DomainTheory.Neighborhood.ApproximableExercises
import Mathlib.Computability.PartrecBasis
import DomainTheory.Neighborhood.Theorem56Full.Basic


namespace DomainTheory.Neighborhood.Theorem56Full

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap
open DomainTheory.Neighborhood.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)
open DomainTheory.Neighborhood.Exercise326 (cond)
open DomainTheory.Neighborhood.Exercise511 (head tail push)
























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
end DomainTheory.Neighborhood.Theorem56Full

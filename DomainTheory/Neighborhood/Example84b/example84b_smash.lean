/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Example84
import DomainTheory.Neighborhood.Definition83
import DomainTheory.Neighborhood.Exercise510
import DomainTheory.Neighborhood.Example84b.Basic
import DomainTheory.Neighborhood.Example84b.smash_subsystem_prod
import DomainTheory.Neighborhood.Example84b.smashRetraction_eq_retractionOfSubsystem


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap ApproximableMap₂

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}





section Smash






/-- **Example 8.4(b)(ii) (Scott 1981, PRG-19).** `smashRetraction` is a projection on `D × E`
whose fixed-point set is isomorphic to the smash product `Exercise510.smash D E`. -/
theorem example84b_smash :
    IsProjection (smashRetraction (D := D) (E := E)) ∧
      Nonempty ((Exercise510.smash D E).Element ≃o
        {z : (prod D E).Element // smashRetraction.toElementMap z = z}) := by
  rw [smashRetraction_eq_retractionOfSubsystem]
  exact ⟨Subsystem.isProjection_retractionOfSubsystem smash_subsystem_prod,
    ⟨Subsystem.elementIso smash_subsystem_prod⟩⟩

end Smash
end DomainTheory.Neighborhood

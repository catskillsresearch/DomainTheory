/-ai
The injection of the projection of an element y lies below y.

The second projection-pair law says that the composite of the injection after the projection lies below the identity. Read on elements, and rewritten through the element map of a composite and of the identity, this is the claim.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise625.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Subsystem

variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem.ProjectionPair

/-- **`g(h(y)) ⊑ y`.** The second projection-pair law `g ∘ h ⊆ I_ℰ`, read on elements. -/
theorem inj_proj_apply_le (P : ProjectionPair D E) (y : E.Element) :
    P.inj.toElementMap (P.proj.toElementMap y) ≤ y := by
  have h := (le_iff_toElementMap_le.mp P.inj_comp_proj_le) y
  rwa [toElementMap_comp, toElementMap_idMap] at h

end Subsystem.ProjectionPair
end DomainTheory.NeighbourhoodSystems

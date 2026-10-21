/-ai
The projection of the injection of an element x equals x.

The composite of the two element maps is the element map of the composite. The first projection-pair law replaces that composite by the identity, and the element map of the identity is the identity.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise625.Basic

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612.proj_comp_inj
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Subsystem

variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem.ProjectionPair

/-- **`h(g(x)) = x`.** The first projection-pair law `h ∘ g = I_𝒟`, read on elements. -/
theorem proj_inj_apply (P : ProjectionPair D E) (x : D.Element) :
    P.proj.toElementMap (P.inj.toElementMap x) = x := by
  rw [← toElementMap_comp, P.proj_comp_inj, toElementMap_idMap]

end Subsystem.ProjectionPair
end DomainTheory.NeighbourhoodSystems

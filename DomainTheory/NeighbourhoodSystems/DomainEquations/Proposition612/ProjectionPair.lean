/-ai
A projection pair from a neighbourhood system D to a neighbourhood system E consists of an approximable injection from D to E and an approximable projection from E to D such that the projection composed after the injection is the identity on D and the injection composed after the projection is contained in the identity on E.
ai-/
module


public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
namespace Subsystem

open NeighborhoodSystem ApproximableMap

variable {α : Type*}

variable {D E : NeighborhoodSystem α}

/-- **A projection pair (Definition 6.13 vocabulary).** Bundles Scott's `i, j` together with the two
laws, ready for reuse in monotone/continuous-on-domains functors and the existence Theorem 6.14. -/
structure ProjectionPair (D E : NeighborhoodSystem α) where
  /-- The injection `i : D → E`. -/
  inj : ApproximableMap D E
  /-- The projection `j : E → D`. -/
  proj : ApproximableMap E D
  /-- `j ∘ i = I_D`. -/
  proj_comp_inj : proj.comp inj = idMap D
  /-- `i ∘ j ⊆ I_E`. -/
  inj_comp_proj_le : inj.comp proj ≤ idMap E

end Subsystem
end DomainTheory.NeighbourhoodSystems

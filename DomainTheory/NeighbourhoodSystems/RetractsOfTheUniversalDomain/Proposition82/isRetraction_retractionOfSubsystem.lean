/-ai
The retraction associated with a subsystem is a retraction: composing it with itself returns it.

The double composite is reassociated so that the projection composed with the injection stands in the middle. That composite is the identity on the subsystem, and composing with the identity leaves the retraction.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition81
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition82.Basic

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612.proj_comp_inj
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem


/-- **Proposition 8.2, first half.** `retractionOfSubsystem h` is a retraction: `a ∘ a = a`, via
`a ∘ a = i∘(j∘i)∘j = i∘I_D∘j = i∘j = a`. -/
theorem isRetraction_retractionOfSubsystem (h : D ◁ E) :
    IsRetraction (retractionOfSubsystem h) := by
  show (h.inj.comp h.proj).comp (h.inj.comp h.proj) = h.inj.comp h.proj
  rw [comp_assoc, ← comp_assoc h.proj h.inj h.proj, h.proj_comp_inj, idMap_comp]

end Subsystem
end DomainTheory.NeighbourhoodSystems

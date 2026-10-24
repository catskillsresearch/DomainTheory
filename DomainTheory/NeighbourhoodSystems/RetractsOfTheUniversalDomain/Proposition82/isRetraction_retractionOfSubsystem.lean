module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition81
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition82.retractionOfSubsystem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition82.elementIso
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition82.retractionOfSubsystem_rel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition82.retractionOfSubsystem_toElementMap_inj

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612.proj_comp_inj
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem


/-- **Proposition 8.2, first half.** `retractionOfSubsystem h` is a retraction: `a ∘ a = a`, via
`a ∘ a = i∘(j∘i)∘j = i∘I_D∘j = i∘j = a`. -/
theorem isRetraction_retractionOfSubsystem (h : D ◁ E) :
    Retraction (retractionOfSubsystem h) := by
  constructor
  show (h.inj.comp h.proj).comp (h.inj.comp h.proj) = h.inj.comp h.proj
  rw [comp_assoc, ← comp_assoc h.proj h.inj h.proj, h.proj_comp_inj, idMap_comp]

end Subsystem
end DomainTheory.NeighbourhoodSystems

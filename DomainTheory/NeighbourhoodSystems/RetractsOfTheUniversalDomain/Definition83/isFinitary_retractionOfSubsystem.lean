/-ai
The retraction of a subsystem is finitary.

The witnessing neighbourhood system is the subsystem itself, and the order isomorphism is the inverse of the element isomorphism between the subsystem and the fixed-point set.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition82
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {D E : NeighborhoodSystem α}




namespace Subsystem

variable {h : D ◁ E}

/-- **Every `retractionOfSubsystem h` is finitary** (Definition 8.3): its fixed-point set is
isomorphic to `|D|` itself, by Proposition 8.2's `elementIso`. -/
theorem isFinitary_retractionOfSubsystem (h : D ◁ E) :
    IsFinitary (retractionOfSubsystem h) :=
  ⟨α, D, ⟨(elementIso h).symm⟩⟩

end Subsystem
end DomainTheory.NeighbourhoodSystems

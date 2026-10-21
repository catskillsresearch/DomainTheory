/-ai
A set of tokens is finitely consistent when every finite subset of it is a consistent set of the information system.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid42

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- A (possibly infinite) set of tokens is *finitely consistent* when every finite subset
lies in `Con`. -/
def IsFinitelyConsistent (U : Set α) : Prop :=
  ∀ Y : Finset α, (Y : Set α) ⊆ U → Y ∈ sys.Con

end InfoSys

end DomainTheory.InformationSystems

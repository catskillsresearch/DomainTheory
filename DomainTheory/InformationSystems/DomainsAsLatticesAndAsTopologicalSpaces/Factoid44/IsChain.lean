module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid43

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- A chain: any two elements are comparable. -/
def IsChain (S : Set sys.Element) : Prop :=
  ∀ (x y : sys.Element), x ∈ S → y ∈ S → x ≤ y ∨ y ≤ x

end InfoSys

end DomainTheory.InformationSystems

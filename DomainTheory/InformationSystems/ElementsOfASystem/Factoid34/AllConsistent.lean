/-ai
An information system is all-consistent when every finite set of tokens is consistent.
ai-/

module

public import DomainTheory.InformationSystems.InformationSystems.InfoSys

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- Every finite set of tokens is consistent. -/
def AllConsistent : Prop := ∀ u : Finset α, u ∈ sys.Con

end InfoSys

end DomainTheory.InformationSystems

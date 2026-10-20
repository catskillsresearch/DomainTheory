module

public import DomainTheory.InformationSystems.InformationSystems.InfoSys

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- A **total** element is a maximal element of `|A|` under inclusion. -/
def IsTotal (x : sys.Element) : Prop := ∀ y, x ≤ y → y ≤ x

end InfoSys

end DomainTheory.InformationSystems

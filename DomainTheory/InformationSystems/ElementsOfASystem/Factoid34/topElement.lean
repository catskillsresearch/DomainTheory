/-ai
When every finite set of tokens is consistent, the top element is the element whose carrier is the whole token set. Consistency of a finite set is the all-consistency hypothesis, and every token belongs to the carrier, so the element is deductively closed.
ai-/

module

public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34.AllConsistent

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- **Factoid 3.4.** When every finite set is consistent, the top element is `D` itself. -/
def topElement (h : sys.AllConsistent) : sys.Element where
  carrier := Set.univ
  consistent := fun Y _ => h Y
  closed := fun _ _ _ _ => trivial

end InfoSys

end DomainTheory.InformationSystems

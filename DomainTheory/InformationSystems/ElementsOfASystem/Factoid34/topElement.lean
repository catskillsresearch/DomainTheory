
module

public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34.AllConsistent

@[expose] public section

namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

def topElement (h : sys.AllConsistent) : sys.Element where
  carrier := Set.univ
  consistent := fun Y _ => h Y
  closed := fun _ _ _ _ => trivial

end InfoSys

end DomainTheory.InformationSystems

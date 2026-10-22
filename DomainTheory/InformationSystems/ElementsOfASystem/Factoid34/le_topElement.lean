
module

public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)


theorem le_topElement (h : sys.AllConsistent) (x : sys.Element) :
    x ≤ sys.topElement h := fun _ _ => trivial

end InfoSys
end DomainTheory.InformationSystems

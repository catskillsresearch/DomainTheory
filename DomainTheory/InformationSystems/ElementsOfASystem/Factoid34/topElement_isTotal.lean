
module

public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34.IsTotal
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34.AllConsistent
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34.topElement
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34.le_topElement

@[expose] public section

namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

theorem topElement_isTotal (h : sys.AllConsistent) :
    sys.IsTotal (sys.topElement h) := fun y _ => sys.le_topElement h y

end InfoSys
end DomainTheory.InformationSystems

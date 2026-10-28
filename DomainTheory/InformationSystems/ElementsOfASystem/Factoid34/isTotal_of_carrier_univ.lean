
module

public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34.IsTotal
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34.AllConsistent
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34.topElement

@[expose] public section

namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

theorem isTotal_of_carrier_univ {x : sys.Element} (hx : x.carrier = Set.univ) :
    sys.IsTotal x := fun _ _ _ _ => hx ▸ trivial

end InfoSys
end DomainTheory.InformationSystems

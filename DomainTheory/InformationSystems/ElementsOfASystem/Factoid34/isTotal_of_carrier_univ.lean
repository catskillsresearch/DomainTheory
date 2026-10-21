/-ai
An element whose carrier is the whole token set is total.

Every token of every element lies in that carrier, so every element lies below it.
ai-/

module

public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)




/-- An element whose carrier is the whole token set is total (hence the greatest element). -/
theorem isTotal_of_carrier_univ {x : sys.Element} (hx : x.carrier = Set.univ) :
    sys.IsTotal x := fun _ _ _ _ => hx ▸ trivial

end InfoSys
end DomainTheory.InformationSystems

module

public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)




/-- Conversely: any total element equals an element with carrier `D`. -/
theorem eq_of_carrier_univ_of_isTotal {x t : sys.Element}
    (hx : x.carrier = Set.univ) (ht : sys.IsTotal t) : t = x :=
  le_antisymm (fun _ _ => hx ▸ trivial) (ht x (fun _ _ => hx ▸ trivial))

end InfoSys
end DomainTheory.InformationSystems

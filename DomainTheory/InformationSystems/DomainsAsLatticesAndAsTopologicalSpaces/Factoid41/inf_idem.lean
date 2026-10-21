/-ai
The meet of an element with itself equals that element.

The criterion that the order is equality with a meet applies to reflexivity of the order.
ai-/
module

public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid41.Basic
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid41.le_iff_inf_eq

@[expose] public section


namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)


theorem inf_idem (x : sys.Element) : sys.inf x x = x :=
  (sys.le_iff_inf_eq (y := x)).1 (le_refl x)

end InfoSys
end DomainTheory.InformationSystems

module

public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid41.inf
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid41.le_iff_inf_eq

@[expose] public section

namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

theorem botElement_inf (x : sys.Element) : sys.inf sys.botElement x = sys.botElement :=
  (sys.le_iff_inf_eq (x := sys.botElement) (y := x)).1 (botElement.le sys x)

end InfoSys
end DomainTheory.InformationSystems

module

public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid41.Basic
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid41.inf_comm
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid41.botElement_inf

@[expose] public section


namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)


theorem inf_botElement (x : sys.Element) : sys.inf x sys.botElement = sys.botElement := by
  rw [sys.inf_comm, sys.botElement_inf]

end InfoSys
end DomainTheory.InformationSystems

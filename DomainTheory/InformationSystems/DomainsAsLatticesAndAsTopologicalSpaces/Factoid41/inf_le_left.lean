module

public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid41.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)


theorem inf_le_left (x y : sys.Element) : sys.inf x y ≤ x :=
  Set.inter_subset_left

end InfoSys
end DomainTheory.InformationSystems

module

public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid41.inf
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid41.le_inf

@[expose] public section

namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

theorem inf_comm (x y : sys.Element) : sys.inf x y = sys.inf y x := by
  refine le_antisymm ?_ ?_
  · exact sys.le_inf (inf.le_right sys x y) (inf.le_left sys x y)
  · exact sys.le_inf (inf.le_right sys y x) (inf.le_left sys y x)

end InfoSys
end DomainTheory.InformationSystems

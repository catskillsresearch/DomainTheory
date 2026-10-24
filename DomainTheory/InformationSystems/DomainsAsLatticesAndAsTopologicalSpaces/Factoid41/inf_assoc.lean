module

public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid41.inf
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid41.le_inf

@[expose] public section


namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)


theorem inf_assoc (x y z : sys.Element) : sys.inf (sys.inf x y) z = sys.inf x (sys.inf y z) := by
  refine le_antisymm ?_ ?_
  · refine sys.le_inf ?_ (sys.le_inf ?_ ?_)
    · exact le_trans (inf.le_left sys _ _) (inf.le_left sys _ _)
    · exact le_trans (inf.le_left sys _ _) (inf.le_right sys _ _)
    · exact inf.le_right sys _ _
  · refine sys.le_inf (sys.le_inf ?_ ?_) ?_
    · exact inf.le_left sys _ _
    · exact le_trans (inf.le_right sys _ _) (inf.le_left sys _ _)
    · exact le_trans (inf.le_right sys _ _) (inf.le_right sys _ _)

end InfoSys
end DomainTheory.InformationSystems

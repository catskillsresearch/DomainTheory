/-ai
The meet of two elements lies below the left argument.

The carrier of the meet is the intersection, which is contained in the left carrier.
ai-/
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

/-ai
The meet of two elements lies below the right argument.

The carrier of the meet is the intersection, which is contained in the right carrier.
ai-/
module

public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid41.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)


theorem inf_le_right (x y : sys.Element) : sys.inf x y ≤ y :=
  Set.inter_subset_right

end InfoSys
end DomainTheory.InformationSystems

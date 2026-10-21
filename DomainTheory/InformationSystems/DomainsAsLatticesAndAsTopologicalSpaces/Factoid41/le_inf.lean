/-ai
An element that lies below both arguments of a meet lies below the meet.

A token of that element lies in both arguments, hence in their intersection.
ai-/
module

public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid41.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)


theorem le_inf {x y z : sys.Element} (hxy : x ≤ y) (hxz : x ≤ z) : x ≤ sys.inf y z :=
  fun _ ha => ⟨hxy ha, hxz ha⟩

end InfoSys
end DomainTheory.InformationSystems

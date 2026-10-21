/-ai
An element that lies below every member of a nonempty family lies below the meet of the family.

A token of that element belongs to every member, hence belongs to the intersection.
ai-/
module

public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid41
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid42.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)


theorem le_familyInf (S : Set sys.Element) (hne : S.Nonempty) {z : sys.Element}
    (h : ∀ x ∈ S, z ≤ x) : z ≤ sys.familyInf S hne :=
  fun _a ha x hx => h x hx ha

end InfoSys
end DomainTheory.InformationSystems

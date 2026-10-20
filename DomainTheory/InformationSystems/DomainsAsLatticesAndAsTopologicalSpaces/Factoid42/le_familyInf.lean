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

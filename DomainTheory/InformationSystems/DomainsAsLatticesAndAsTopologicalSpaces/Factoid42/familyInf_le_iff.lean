module

public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid41
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid42.Basic
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid42.familyInf_le
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid42.le_familyInf

@[expose] public section


namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)



/-- `familyInf` is the greatest lower bound of the family. -/
theorem familyInf_le_iff (S : Set sys.Element) (hne : S.Nonempty) {z : sys.Element} :
    z ≤ sys.familyInf S hne ↔ ∀ x ∈ S, z ≤ x :=
  ⟨fun hz _x hx => le_trans hz (sys.familyInf_le S hne hx), sys.le_familyInf S hne⟩

end InfoSys
end DomainTheory.InformationSystems

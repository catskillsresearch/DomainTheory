module

public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid41
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid42.familyInfCarrier
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid42.familyInf
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid42.le_familyInf

@[expose] public section

namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

theorem familyInf.le_iff (S : Set sys.Element) (hne : S.Nonempty) {z : sys.Element} :
    z ≤ sys.familyInf S hne ↔ ∀ x ∈ S, z ≤ x :=
  ⟨fun hz _x hx => le_trans hz (familyInf.le sys S hne hx), sys.le_familyInf S hne⟩

end InfoSys
end DomainTheory.InformationSystems

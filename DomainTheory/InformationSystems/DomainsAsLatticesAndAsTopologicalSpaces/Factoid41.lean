module

public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid41.inf

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys

theorem factoid_41 :
    ∀ {α : Type*} [DecidableEq α] (sys : InfoSys α) {x y : sys.Element},
      x ≤ y ↔ sys.inf x y = x :=
  @inf.le_iff_eq

end DomainTheory.InformationSystems.InfoSys

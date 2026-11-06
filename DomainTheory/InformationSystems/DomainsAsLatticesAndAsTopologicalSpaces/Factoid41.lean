module

public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid41.le_iff_inf_eq

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys

theorem theorem_41 :
    ∀ {α : Type*} [DecidableEq α] (sys : InfoSys α) {x y : sys.Element},
      x ≤ y ↔ sys.inf x y = x :=
  @le_iff_inf_eq

end DomainTheory.InformationSystems.InfoSys

module

public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.chainSup

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys

theorem factoid_44 :
    ∀ {α : Type*} [DecidableEq α] (sys : InfoSys α) (S : Set sys.Element)
      (hne : S.Nonempty) (hdir : sys.IsDirected S),
      (sys.directedSup S hne hdir).carrier = sys.familyUnionCarrier S :=
  @directedSup.carrier_eq_union

end DomainTheory.InformationSystems.InfoSys

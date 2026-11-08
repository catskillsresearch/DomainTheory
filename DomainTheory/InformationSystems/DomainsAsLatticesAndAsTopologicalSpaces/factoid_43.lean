module

public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.join

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys

theorem factoid_43 :
    ∀ {α : Type*} [DecidableEq α] (sys : InfoSys α) (x y : sys.Element),
      (∃ z : sys.Element, x ≤ z ∧ y ≤ z) ↔
        Nonempty (sys.IsFinitelyConsistent (x.carrier ∪ y.carrier)) :=
  @join.exists_iff

end DomainTheory.InformationSystems.InfoSys

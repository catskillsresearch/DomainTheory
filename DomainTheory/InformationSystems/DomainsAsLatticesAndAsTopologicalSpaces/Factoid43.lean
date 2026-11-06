module

public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid43.exists_join_iff

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys

theorem theorem_43 :
    ∀ {α : Type*} [DecidableEq α] (sys : InfoSys α) (x y : sys.Element),
      (∃ z : sys.Element, x ≤ z ∧ y ≤ z) ↔
        Nonempty (sys.IsFinitelyConsistent (x.carrier ∪ y.carrier)) :=
  @exists_join_iff

end DomainTheory.InformationSystems.InfoSys

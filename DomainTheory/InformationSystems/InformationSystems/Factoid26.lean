module

public import DomainTheory.InformationSystems.InformationSystems.Factoid26.consistent_empty

@[expose] public section

namespace DomainTheory.InformationSystems.Factoid26

theorem theorem_26 :
    ∀ {A B : Type*}, Consistent (∅ : Finset (Token A B)) :=
  @consistent_empty

end DomainTheory.InformationSystems.Factoid26

module

public import DomainTheory.InformationSystems.InformationSystems.Factoid26.consistent_empty

@[expose] public section

namespace DomainTheory.InformationSystems.Factoid26

set_option linter.unusedVariables false

theorem theorem_26.{u_1, u_2} : ∀ {A : Type u_1} {B : Type u_2},
  @DomainTheory.InformationSystems.Factoid26.Consistent A B
    (@EmptyCollection.emptyCollection (Finset (DomainTheory.InformationSystems.Factoid26.Token A B))
      (@Finset.instEmptyCollection (DomainTheory.InformationSystems.Factoid26.Token A B))) :=
  @DomainTheory.InformationSystems.Factoid26.consistent_empty

end DomainTheory.InformationSystems.Factoid26

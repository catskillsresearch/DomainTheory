module

public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34.exists_top_iff_allConsistent

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys

set_option linter.unusedVariables false

theorem theorem_34.{u_1} : ∀ {α : Type u_1} [inst : DecidableEq α] (sys : @DomainTheory.InformationSystems.InfoSys α inst),
  Iff
    (∃ (x : @DomainTheory.InformationSystems.InfoSys.Element α inst sys),
      @Eq (Set α) (@DomainTheory.InformationSystems.InfoSys.Element.carrier α inst sys x) (@Set.univ α))
    (@DomainTheory.InformationSystems.InfoSys.AllConsistent α inst sys) :=
  @DomainTheory.InformationSystems.InfoSys.exists_top_iff_allConsistent

end DomainTheory.InformationSystems.InfoSys

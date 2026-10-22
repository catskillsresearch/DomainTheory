module

public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid36.element_eq_approxUnion
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid36.mem_element_iff_mem_closure

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys

set_option linter.unusedVariables false

theorem theorem_36.{u_1} : And
  (∀ {α : Type u_1} [inst : DecidableEq α] (sys : @DomainTheory.InformationSystems.InfoSys α inst)
    (x : @DomainTheory.InformationSystems.InfoSys.Element α inst sys),
    @Eq (Set α) (@DomainTheory.InformationSystems.InfoSys.Element.carrier α inst sys x)
      (@DomainTheory.InformationSystems.InfoSys.approxUnion α inst sys x))
  (∀ {α : Type u_1} [inst : DecidableEq α] (sys : @DomainTheory.InformationSystems.InfoSys α inst)
    (x : @DomainTheory.InformationSystems.InfoSys.Element α inst sys) (a : α),
    Iff
      (@Membership.mem α (Set α) (@Set.instMembership α)
        (@DomainTheory.InformationSystems.InfoSys.Element.carrier α inst sys x) a)
      (@Membership.mem α (Set α) (@Set.instMembership α)
        (@DomainTheory.InformationSystems.InfoSys.approxUnion α inst sys x) a)) :=
  @And.intro
  (∀ {α : Type u_1} [inst : DecidableEq α] (sys : @DomainTheory.InformationSystems.InfoSys α inst)
    (x : @DomainTheory.InformationSystems.InfoSys.Element α inst sys),
    @Eq (Set α) (@DomainTheory.InformationSystems.InfoSys.Element.carrier α inst sys x)
      (@DomainTheory.InformationSystems.InfoSys.approxUnion α inst sys x))
  (∀ {α : Type u_1} [inst : DecidableEq α] (sys : @DomainTheory.InformationSystems.InfoSys α inst)
    (x : @DomainTheory.InformationSystems.InfoSys.Element α inst sys) (a : α),
    Iff
      (@Membership.mem α (Set α) (@Set.instMembership α)
        (@DomainTheory.InformationSystems.InfoSys.Element.carrier α inst sys x) a)
      (@Membership.mem α (Set α) (@Set.instMembership α)
        (@DomainTheory.InformationSystems.InfoSys.approxUnion α inst sys x) a))
  @DomainTheory.InformationSystems.InfoSys.element_eq_approxUnion
  @DomainTheory.InformationSystems.InfoSys.mem_element_iff_mem_closure

end DomainTheory.InformationSystems.InfoSys

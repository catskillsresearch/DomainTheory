/-ai
Every element contains the bottom token.

The numbered name theorem_32 is that statement.
ai-/
module

public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid32.factoid_3_2

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys

set_option linter.unusedVariables false

theorem theorem_32.{u_1} : ∀ {α : Type u_1} [inst : DecidableEq α] (sys : @DomainTheory.InformationSystems.InfoSys α inst)
  (x : @DomainTheory.InformationSystems.InfoSys.Element α inst sys),
  @Membership.mem α (Set α) (@Set.instMembership α)
    (@DomainTheory.InformationSystems.InfoSys.Element.carrier α inst sys x)
    (@DomainTheory.InformationSystems.InfoSys.bot α inst sys) :=
  @DomainTheory.InformationSystems.InfoSys.factoid_3_2

end DomainTheory.InformationSystems.InfoSys

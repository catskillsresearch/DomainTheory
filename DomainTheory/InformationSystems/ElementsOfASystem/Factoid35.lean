/-ai
A consistent finite set is contained in its entailment closure.

The numbered name theorem_35 is that statement.
ai-/
module

public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35.subset_closure

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys

set_option linter.unusedVariables false

theorem theorem_35.{u_1} : ∀ {α : Type u_1} [inst : DecidableEq α] (sys : @DomainTheory.InformationSystems.InfoSys α inst) {u : Finset α}
  (hu :
    @Membership.mem (Finset α) (Set (Finset α)) (@Set.instMembership (Finset α))
      (@DomainTheory.InformationSystems.InfoSys.Con α inst sys) u),
  @LE.le (Set α) (@Set.instLE α) (@SetLike.coe (Finset α) α (@Finset.instSetLike α) u)
    (@DomainTheory.InformationSystems.InfoSys.Element.carrier α inst sys
      (@DomainTheory.InformationSystems.InfoSys.closure α inst sys u hu)) :=
  @DomainTheory.InformationSystems.InfoSys.subset_closure

end DomainTheory.InformationSystems.InfoSys

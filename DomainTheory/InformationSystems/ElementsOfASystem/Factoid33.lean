/-ai
The bottom element lies below every element.

The numbered name theorem_33 is that statement.
ai-/
module

public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33.botElement_le

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys

set_option linter.unusedVariables false

theorem theorem_33.{u_1} : ∀ {α : Type u_1} [inst : DecidableEq α] (sys : @DomainTheory.InformationSystems.InfoSys α inst)
  (x : @DomainTheory.InformationSystems.InfoSys.Element α inst sys),
  @LE.le (@DomainTheory.InformationSystems.InfoSys.Element α inst sys)
    (@Preorder.toLE (@DomainTheory.InformationSystems.InfoSys.Element α inst sys)
      (@PartialOrder.toPreorder (@DomainTheory.InformationSystems.InfoSys.Element α inst sys)
        (@DomainTheory.InformationSystems.InfoSys.instPartialOrderElement α inst sys)))
    (@DomainTheory.InformationSystems.InfoSys.botElement α inst sys) x :=
  @DomainTheory.InformationSystems.InfoSys.botElement_le

end DomainTheory.InformationSystems.InfoSys

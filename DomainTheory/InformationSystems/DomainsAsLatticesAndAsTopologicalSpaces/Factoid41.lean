module

public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid41.le_iff_inf_eq

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys

set_option linter.unusedVariables false

theorem theorem_41.{u_1} : ∀ {α : Type u_1} [inst : DecidableEq α] (sys : @DomainTheory.InformationSystems.InfoSys α inst)
  {x y : @DomainTheory.InformationSystems.InfoSys.Element α inst sys},
  Iff
    (@LE.le (@DomainTheory.InformationSystems.InfoSys.Element α inst sys)
      (@Preorder.toLE (@DomainTheory.InformationSystems.InfoSys.Element α inst sys)
        (@PartialOrder.toPreorder (@DomainTheory.InformationSystems.InfoSys.Element α inst sys)
          (@DomainTheory.InformationSystems.InfoSys.instPartialOrderElement α inst sys)))
      x y)
    (@Eq (@DomainTheory.InformationSystems.InfoSys.Element α inst sys)
      (@DomainTheory.InformationSystems.InfoSys.inf α inst sys x y) x) :=
  @DomainTheory.InformationSystems.InfoSys.le_iff_inf_eq

end DomainTheory.InformationSystems.InfoSys

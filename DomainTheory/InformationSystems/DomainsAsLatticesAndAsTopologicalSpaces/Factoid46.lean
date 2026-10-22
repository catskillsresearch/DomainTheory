module

public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid46.toElement_ofScottContinuous

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys.ApproximableMap

set_option linter.unusedVariables false

theorem theorem_46.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} [inst : DecidableEq α] [inst_1 : DecidableEq β]
  {A : @DomainTheory.InformationSystems.InfoSys α inst} {B : @DomainTheory.InformationSystems.InfoSys β inst_1}
  (g : @DomainTheory.InformationSystems.InfoSys.ScottContinuous α β inst inst_1 A B)
  (x : @DomainTheory.InformationSystems.InfoSys.Element α inst A),
  @Eq (@DomainTheory.InformationSystems.InfoSys.Element β inst_1 B)
    (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement α β inst inst_1 A B
      (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.ofScottContinuous α β inst inst_1 A B g) x)
    (@DomainTheory.InformationSystems.InfoSys.ScottContinuous.toFun α β inst inst_1 A B g x) :=
  @DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement_ofScottContinuous

end DomainTheory.InformationSystems.InfoSys.ApproximableMap

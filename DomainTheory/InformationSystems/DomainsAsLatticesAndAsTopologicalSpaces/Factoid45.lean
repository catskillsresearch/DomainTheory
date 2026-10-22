module

public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid45.eq_directedSup_finiteApproximants

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys

set_option linter.unusedVariables false

theorem theorem_45.{u_1} : ∀ {α : Type u_1} [inst : DecidableEq α] (sys : @DomainTheory.InformationSystems.InfoSys α inst)
  (x : @DomainTheory.InformationSystems.InfoSys.Element α inst sys),
  @Eq (@DomainTheory.InformationSystems.InfoSys.Element α inst sys) x
    (@DomainTheory.InformationSystems.InfoSys.directedSup α inst sys
      (@DomainTheory.InformationSystems.InfoSys.finiteApproximants α inst sys x)
      (@DomainTheory.InformationSystems.InfoSys.nonempty_finiteApproximants α inst sys x)
      (@DomainTheory.InformationSystems.InfoSys.directed_finiteApproximants α inst sys x)) :=
  @DomainTheory.InformationSystems.InfoSys.eq_directedSup_finiteApproximants

end DomainTheory.InformationSystems.InfoSys

module

public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid42.familyInf_pair

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys

set_option linter.unusedVariables false

theorem theorem_42.{u_1} : ∀ {α : Type u_1} [inst : DecidableEq α] (sys : @DomainTheory.InformationSystems.InfoSys α inst)
  (x y : @DomainTheory.InformationSystems.InfoSys.Element α inst sys),
  @Eq (@DomainTheory.InformationSystems.InfoSys.Element α inst sys)
    (@DomainTheory.InformationSystems.InfoSys.familyInf α inst sys
      (@Insert.insert (@DomainTheory.InformationSystems.InfoSys.Element α inst sys)
        (Set (@DomainTheory.InformationSystems.InfoSys.Element α inst sys))
        (@Set.instInsert (@DomainTheory.InformationSystems.InfoSys.Element α inst sys)) x
        (@Singleton.singleton (@DomainTheory.InformationSystems.InfoSys.Element α inst sys)
          (Set (@DomainTheory.InformationSystems.InfoSys.Element α inst sys))
          (@Set.instSingletonSet (@DomainTheory.InformationSystems.InfoSys.Element α inst sys)) y))
      (@Exists.intro (@DomainTheory.InformationSystems.InfoSys.Element α inst sys)
        (fun (x_1 : @DomainTheory.InformationSystems.InfoSys.Element α inst sys) =>
          @Membership.mem (@DomainTheory.InformationSystems.InfoSys.Element α inst sys)
            (Set (@DomainTheory.InformationSystems.InfoSys.Element α inst sys))
            (@Set.instMembership (@DomainTheory.InformationSystems.InfoSys.Element α inst sys))
            (@Insert.insert (@DomainTheory.InformationSystems.InfoSys.Element α inst sys)
              (Set (@DomainTheory.InformationSystems.InfoSys.Element α inst sys))
              (@Set.instInsert (@DomainTheory.InformationSystems.InfoSys.Element α inst sys)) x
              (@Singleton.singleton (@DomainTheory.InformationSystems.InfoSys.Element α inst sys)
                (Set (@DomainTheory.InformationSystems.InfoSys.Element α inst sys))
                (@Set.instSingletonSet (@DomainTheory.InformationSystems.InfoSys.Element α inst sys)) y))
            x_1)
        x
        (@Set.mem_insert (@DomainTheory.InformationSystems.InfoSys.Element α inst sys) x
          (@Singleton.singleton (@DomainTheory.InformationSystems.InfoSys.Element α inst sys)
            (Set (@DomainTheory.InformationSystems.InfoSys.Element α inst sys))
            (@Set.instSingletonSet (@DomainTheory.InformationSystems.InfoSys.Element α inst sys)) y))))
    (@DomainTheory.InformationSystems.InfoSys.inf α inst sys x y) :=
  @DomainTheory.InformationSystems.InfoSys.familyInf_pair

end DomainTheory.InformationSystems.InfoSys

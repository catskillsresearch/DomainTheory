module

public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid44.directedSup

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys

set_option linter.unusedVariables false

theorem theorem_44.{u_1} : ∀ {α : Type u_1} [inst : DecidableEq α] (sys : @DomainTheory.InformationSystems.InfoSys α inst)
  (S : Set (@DomainTheory.InformationSystems.InfoSys.Element α inst sys))
  (hne : @Set.Nonempty (@DomainTheory.InformationSystems.InfoSys.Element α inst sys) S)
  (hdir : @DomainTheory.InformationSystems.InfoSys.IsDirected α inst sys S),
  @Eq (Set α)
    (@DomainTheory.InformationSystems.InfoSys.Element.carrier α inst sys
      (@DomainTheory.InformationSystems.InfoSys.directedSup α inst sys S hne hdir))
    (@DomainTheory.InformationSystems.InfoSys.familyUnionCarrier α inst sys S) :=
  @DomainTheory.InformationSystems.InfoSys.directedSup.carrier_eq_union

end DomainTheory.InformationSystems.InfoSys

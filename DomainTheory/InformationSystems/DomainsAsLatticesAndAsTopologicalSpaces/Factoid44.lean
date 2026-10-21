/-ai
For a nonempty directed family of elements, the carrier of the directed supremum equals the union of the carriers.

The numbered name theorem_44 is that statement.
ai-/
module

public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid44.directedSup_carrier_eq_union

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
  @DomainTheory.InformationSystems.InfoSys.directedSup_carrier_eq_union

end DomainTheory.InformationSystems.InfoSys

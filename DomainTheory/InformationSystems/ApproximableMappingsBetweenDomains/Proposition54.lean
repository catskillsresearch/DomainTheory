/-ai
Proposition 5.4(ii) states that the identity approximable mapping sends every element to itself.

The numbered name theorem_54 is that statement.
ai-/
module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition54.idMap_toElement

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys

set_option linter.unusedVariables false

theorem theorem_54.{u_1} : ∀ {α : Type u_1} [inst : DecidableEq α] (A : @DomainTheory.InformationSystems.InfoSys α inst)
  (x : @DomainTheory.InformationSystems.InfoSys.Element α inst A),
  @Eq (@DomainTheory.InformationSystems.InfoSys.Element α inst A)
    (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement α α inst inst A A
      (@DomainTheory.InformationSystems.InfoSys.idMap α inst A) x)
    x :=
  @DomainTheory.InformationSystems.InfoSys.idMap_toElement

end DomainTheory.InformationSystems.InfoSys

/-ai
Evaluating the constant map at an element b on the least element of the unit returns b.

The numbered name theorem_65 is that statement.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Factoid65.toElement_constMap_bot

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys.ApproximableMap

set_option linter.unusedVariables false

theorem theorem_65.{u_1, u_2} : ∀ {α : Type u_1} [inst : DecidableEq α] {A : @DomainTheory.InformationSystems.InfoSys α inst}
  (b : @DomainTheory.InformationSystems.InfoSys.Element α inst A),
  @Eq (@DomainTheory.InformationSystems.InfoSys.Element α inst A)
    (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement PUnit.{u_2 + 1} α instDecidableEqPUnit inst
      DomainTheory.InformationSystems.InfoSys.unitSystem A
      (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.constMap PUnit.{u_2 + 1} α instDecidableEqPUnit inst
        DomainTheory.InformationSystems.InfoSys.unitSystem A b)
      (@DomainTheory.InformationSystems.InfoSys.botElement PUnit.{u_2 + 1} instDecidableEqPUnit
        DomainTheory.InformationSystems.InfoSys.unitSystem))
    b :=
  @DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement_constMap_bot

end DomainTheory.InformationSystems.InfoSys.ApproximableMap

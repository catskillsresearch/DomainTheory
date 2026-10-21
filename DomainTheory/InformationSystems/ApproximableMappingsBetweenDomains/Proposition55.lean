/-ai
Proposition 5.5(ii) states that the image of an element under a composite equals the image under the outer mapping of the image under the inner mapping.

The numbered name theorem_55 is that statement.
ai-/
module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55.comp_toElement

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys.ApproximableMap

set_option linter.unusedVariables false

theorem theorem_55.{u_1, u_2, u_3} : ∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : DecidableEq α] [inst_1 : DecidableEq β] [inst_2 : DecidableEq γ]
  {A : @DomainTheory.InformationSystems.InfoSys α inst} {B : @DomainTheory.InformationSystems.InfoSys β inst_1}
  {C : @DomainTheory.InformationSystems.InfoSys γ inst_2}
  (g : @DomainTheory.InformationSystems.InfoSys.ApproximableMap β γ inst_1 inst_2 B C)
  (f : @DomainTheory.InformationSystems.InfoSys.ApproximableMap α β inst inst_1 A B)
  (x : @DomainTheory.InformationSystems.InfoSys.Element α inst A),
  @Eq (@DomainTheory.InformationSystems.InfoSys.Element γ inst_2 C)
    (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement α γ inst inst_2 A C
      (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.comp α β γ inst inst_1 inst_2 A B C g f) x)
    (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement β γ inst_1 inst_2 B C g
      (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement α β inst inst_1 A B f x)) :=
  @DomainTheory.InformationSystems.InfoSys.ApproximableMap.comp_toElement

end DomainTheory.InformationSystems.InfoSys.ApproximableMap

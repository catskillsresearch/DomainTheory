module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition56.constMap_toElement
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition56.comp_constMap
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition56.constMap_comp

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys.ApproximableMap

set_option linter.unusedVariables false

theorem theorem_56.{u_1, u_2, u_3, u_4} : And
  (And
    (∀ {α : Type u_1} {β : Type u_2} [inst : DecidableEq α] [inst_1 : DecidableEq β]
      {A : @DomainTheory.InformationSystems.InfoSys α inst} {B : @DomainTheory.InformationSystems.InfoSys β inst_1}
      (b : @DomainTheory.InformationSystems.InfoSys.Element β inst_1 B)
      (x : @DomainTheory.InformationSystems.InfoSys.Element α inst A),
      @Eq (@DomainTheory.InformationSystems.InfoSys.Element β inst_1 B)
        (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement α β inst inst_1 A B
          (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.constMap α β inst inst_1 A B b) x)
        b)
    (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : DecidableEq α] [inst_1 : DecidableEq β]
      [inst_2 : DecidableEq γ] {A : @DomainTheory.InformationSystems.InfoSys α inst}
      {B : @DomainTheory.InformationSystems.InfoSys β inst_1} {C : @DomainTheory.InformationSystems.InfoSys γ inst_2}
      (f : @DomainTheory.InformationSystems.InfoSys.ApproximableMap β γ inst_1 inst_2 B C)
      (b : @DomainTheory.InformationSystems.InfoSys.Element β inst_1 B),
      @Eq (@DomainTheory.InformationSystems.InfoSys.ApproximableMap α γ inst inst_2 A C)
        (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.comp α β γ inst inst_1 inst_2 A B C f
          (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.constMap α β inst inst_1 A B b))
        (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.constMap α γ inst inst_2 A C
          (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement β γ inst_1 inst_2 B C f b))))
  (∀ {α : Type u_1} {β : Type u_2} {δ : Type u_4} [inst : DecidableEq α] [inst_1 : DecidableEq β]
    [inst_2 : DecidableEq δ] {A : @DomainTheory.InformationSystems.InfoSys α inst}
    {B : @DomainTheory.InformationSystems.InfoSys β inst_1} {D : @DomainTheory.InformationSystems.InfoSys δ inst_2}
    (b : @DomainTheory.InformationSystems.InfoSys.Element β inst_1 B)
    (g : @DomainTheory.InformationSystems.InfoSys.ApproximableMap δ α inst_2 inst D A),
    @Eq (@DomainTheory.InformationSystems.InfoSys.ApproximableMap δ β inst_2 inst_1 D B)
      (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.comp δ α β inst_2 inst inst_1 D A B
        (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.constMap α β inst inst_1 A B b) g)
      (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.constMap δ β inst_2 inst_1 D B b)) :=
  @And.intro
  (And
    (∀ {α : Type u_1} {β : Type u_2} [inst : DecidableEq α] [inst_1 : DecidableEq β]
      {A : @DomainTheory.InformationSystems.InfoSys α inst} {B : @DomainTheory.InformationSystems.InfoSys β inst_1}
      (b : @DomainTheory.InformationSystems.InfoSys.Element β inst_1 B)
      (x : @DomainTheory.InformationSystems.InfoSys.Element α inst A),
      @Eq (@DomainTheory.InformationSystems.InfoSys.Element β inst_1 B)
        (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement α β inst inst_1 A B
          (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.constMap α β inst inst_1 A B b) x)
        b)
    (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : DecidableEq α] [inst_1 : DecidableEq β]
      [inst_2 : DecidableEq γ] {A : @DomainTheory.InformationSystems.InfoSys α inst}
      {B : @DomainTheory.InformationSystems.InfoSys β inst_1} {C : @DomainTheory.InformationSystems.InfoSys γ inst_2}
      (f : @DomainTheory.InformationSystems.InfoSys.ApproximableMap β γ inst_1 inst_2 B C)
      (b : @DomainTheory.InformationSystems.InfoSys.Element β inst_1 B),
      @Eq (@DomainTheory.InformationSystems.InfoSys.ApproximableMap α γ inst inst_2 A C)
        (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.comp α β γ inst inst_1 inst_2 A B C f
          (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.constMap α β inst inst_1 A B b))
        (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.constMap α γ inst inst_2 A C
          (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement β γ inst_1 inst_2 B C f b))))
  (∀ {α : Type u_1} {β : Type u_2} {δ : Type u_4} [inst : DecidableEq α] [inst_1 : DecidableEq β]
    [inst_2 : DecidableEq δ] {A : @DomainTheory.InformationSystems.InfoSys α inst}
    {B : @DomainTheory.InformationSystems.InfoSys β inst_1} {D : @DomainTheory.InformationSystems.InfoSys δ inst_2}
    (b : @DomainTheory.InformationSystems.InfoSys.Element β inst_1 B)
    (g : @DomainTheory.InformationSystems.InfoSys.ApproximableMap δ α inst_2 inst D A),
    @Eq (@DomainTheory.InformationSystems.InfoSys.ApproximableMap δ β inst_2 inst_1 D B)
      (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.comp δ α β inst_2 inst inst_1 D A B
        (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.constMap α β inst inst_1 A B b) g)
      (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.constMap δ β inst_2 inst_1 D B b))
  (@And.intro
    (∀ {α : Type u_1} {β : Type u_2} [inst : DecidableEq α] [inst_1 : DecidableEq β]
      {A : @DomainTheory.InformationSystems.InfoSys α inst} {B : @DomainTheory.InformationSystems.InfoSys β inst_1}
      (b : @DomainTheory.InformationSystems.InfoSys.Element β inst_1 B)
      (x : @DomainTheory.InformationSystems.InfoSys.Element α inst A),
      @Eq (@DomainTheory.InformationSystems.InfoSys.Element β inst_1 B)
        (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement α β inst inst_1 A B
          (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.constMap α β inst inst_1 A B b) x)
        b)
    (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : DecidableEq α] [inst_1 : DecidableEq β]
      [inst_2 : DecidableEq γ] {A : @DomainTheory.InformationSystems.InfoSys α inst}
      {B : @DomainTheory.InformationSystems.InfoSys β inst_1} {C : @DomainTheory.InformationSystems.InfoSys γ inst_2}
      (f : @DomainTheory.InformationSystems.InfoSys.ApproximableMap β γ inst_1 inst_2 B C)
      (b : @DomainTheory.InformationSystems.InfoSys.Element β inst_1 B),
      @Eq (@DomainTheory.InformationSystems.InfoSys.ApproximableMap α γ inst inst_2 A C)
        (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.comp α β γ inst inst_1 inst_2 A B C f
          (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.constMap α β inst inst_1 A B b))
        (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.constMap α γ inst inst_2 A C
          (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement β γ inst_1 inst_2 B C f b)))
    @DomainTheory.InformationSystems.InfoSys.ApproximableMap.constMap_toElement
    @DomainTheory.InformationSystems.InfoSys.ApproximableMap.comp_constMap)
  @DomainTheory.InformationSystems.InfoSys.ApproximableMap.constMap_comp

end DomainTheory.InformationSystems.InfoSys.ApproximableMap

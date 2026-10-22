module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Proposition74.proposition_7_4_ii
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Proposition74.proposition_7_4_iii
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Proposition74.proposition_7_4_unique

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys.ApproximableMap

set_option linter.unusedVariables false

theorem theorem_74.{u_1, u_2} : And
  (And
    (∀ {α : Type u_1} [inst : DecidableEq α] (A : @DomainTheory.InformationSystems.InfoSys α inst)
      (f : @DomainTheory.InformationSystems.InfoSys.ApproximableMap α α inst inst A A),
      @Eq (@DomainTheory.InformationSystems.InfoSys.Element α inst A)
        (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement α α inst inst A A f
          (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.fixElement α inst A f))
        (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.fixElement α inst A f))
    (∀ {α : Type u_1} {β : Type u_2} [inst : DecidableEq α] [inst_1 : DecidableEq β]
      (A : @DomainTheory.InformationSystems.InfoSys α inst) (B : @DomainTheory.InformationSystems.InfoSys β inst_1)
      (f : @DomainTheory.InformationSystems.InfoSys.ApproximableMap α α inst inst A A)
      (g : @DomainTheory.InformationSystems.InfoSys.ApproximableMap β β inst_1 inst_1 B B)
      (h : @DomainTheory.InformationSystems.InfoSys.ApproximableMap α β inst inst_1 A B),
      @Eq (@DomainTheory.InformationSystems.InfoSys.ApproximableMap α β inst inst_1 A B)
          (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.comp α α β inst inst inst_1 A A B h f)
          (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.comp α β β inst inst_1 inst_1 A B B g h) →
        @Eq (@DomainTheory.InformationSystems.InfoSys.Element β inst_1 B)
            (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement α β inst inst_1 A B h
              (@DomainTheory.InformationSystems.InfoSys.botElement α inst A))
            (@DomainTheory.InformationSystems.InfoSys.botElement β inst_1 B) →
          @Eq (@DomainTheory.InformationSystems.InfoSys.Element β inst_1 B)
            (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement α β inst inst_1 A B h
              (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.fixElement α inst A f))
            (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.fixElement β inst_1 B g)))
  (∀ {α : Type u_1} [inst : DecidableEq α] (A : @DomainTheory.InformationSystems.InfoSys α inst)
    (f : @DomainTheory.InformationSystems.InfoSys.ApproximableMap α α inst inst A A)
    (φ : @DomainTheory.InformationSystems.InfoSys.Element α inst A),
    @Eq (@DomainTheory.InformationSystems.InfoSys.Element α inst A)
        (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement α α inst inst A A f φ) φ →
      (∀ (x : @DomainTheory.InformationSystems.InfoSys.Element α inst A),
          @LE.le (@DomainTheory.InformationSystems.InfoSys.Element α inst A)
              (@Preorder.toLE (@DomainTheory.InformationSystems.InfoSys.Element α inst A)
                (@PartialOrder.toPreorder (@DomainTheory.InformationSystems.InfoSys.Element α inst A)
                  (@DomainTheory.InformationSystems.InfoSys.instPartialOrderElement α inst A)))
              (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement α α inst inst A A f x) x →
            @LE.le (@DomainTheory.InformationSystems.InfoSys.Element α inst A)
              (@Preorder.toLE (@DomainTheory.InformationSystems.InfoSys.Element α inst A)
                (@PartialOrder.toPreorder (@DomainTheory.InformationSystems.InfoSys.Element α inst A)
                  (@DomainTheory.InformationSystems.InfoSys.instPartialOrderElement α inst A)))
              φ x) →
        @Eq (@DomainTheory.InformationSystems.InfoSys.Element α inst A) φ
          (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.fixElement α inst A f)) :=
  @And.intro
  (And
    (∀ {α : Type u_1} [inst : DecidableEq α] (A : @DomainTheory.InformationSystems.InfoSys α inst)
      (f : @DomainTheory.InformationSystems.InfoSys.ApproximableMap α α inst inst A A),
      @Eq (@DomainTheory.InformationSystems.InfoSys.Element α inst A)
        (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement α α inst inst A A f
          (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.fixElement α inst A f))
        (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.fixElement α inst A f))
    (∀ {α : Type u_1} {β : Type u_2} [inst : DecidableEq α] [inst_1 : DecidableEq β]
      (A : @DomainTheory.InformationSystems.InfoSys α inst) (B : @DomainTheory.InformationSystems.InfoSys β inst_1)
      (f : @DomainTheory.InformationSystems.InfoSys.ApproximableMap α α inst inst A A)
      (g : @DomainTheory.InformationSystems.InfoSys.ApproximableMap β β inst_1 inst_1 B B)
      (h : @DomainTheory.InformationSystems.InfoSys.ApproximableMap α β inst inst_1 A B),
      @Eq (@DomainTheory.InformationSystems.InfoSys.ApproximableMap α β inst inst_1 A B)
          (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.comp α α β inst inst inst_1 A A B h f)
          (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.comp α β β inst inst_1 inst_1 A B B g h) →
        @Eq (@DomainTheory.InformationSystems.InfoSys.Element β inst_1 B)
            (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement α β inst inst_1 A B h
              (@DomainTheory.InformationSystems.InfoSys.botElement α inst A))
            (@DomainTheory.InformationSystems.InfoSys.botElement β inst_1 B) →
          @Eq (@DomainTheory.InformationSystems.InfoSys.Element β inst_1 B)
            (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement α β inst inst_1 A B h
              (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.fixElement α inst A f))
            (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.fixElement β inst_1 B g)))
  (∀ {α : Type u_1} [inst : DecidableEq α] (A : @DomainTheory.InformationSystems.InfoSys α inst)
    (f : @DomainTheory.InformationSystems.InfoSys.ApproximableMap α α inst inst A A)
    (φ : @DomainTheory.InformationSystems.InfoSys.Element α inst A),
    @Eq (@DomainTheory.InformationSystems.InfoSys.Element α inst A)
        (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement α α inst inst A A f φ) φ →
      (∀ (x : @DomainTheory.InformationSystems.InfoSys.Element α inst A),
          @LE.le (@DomainTheory.InformationSystems.InfoSys.Element α inst A)
              (@Preorder.toLE (@DomainTheory.InformationSystems.InfoSys.Element α inst A)
                (@PartialOrder.toPreorder (@DomainTheory.InformationSystems.InfoSys.Element α inst A)
                  (@DomainTheory.InformationSystems.InfoSys.instPartialOrderElement α inst A)))
              (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement α α inst inst A A f x) x →
            @LE.le (@DomainTheory.InformationSystems.InfoSys.Element α inst A)
              (@Preorder.toLE (@DomainTheory.InformationSystems.InfoSys.Element α inst A)
                (@PartialOrder.toPreorder (@DomainTheory.InformationSystems.InfoSys.Element α inst A)
                  (@DomainTheory.InformationSystems.InfoSys.instPartialOrderElement α inst A)))
              φ x) →
        @Eq (@DomainTheory.InformationSystems.InfoSys.Element α inst A) φ
          (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.fixElement α inst A f))
  (@And.intro
    (∀ {α : Type u_1} [inst : DecidableEq α] (A : @DomainTheory.InformationSystems.InfoSys α inst)
      (f : @DomainTheory.InformationSystems.InfoSys.ApproximableMap α α inst inst A A),
      @Eq (@DomainTheory.InformationSystems.InfoSys.Element α inst A)
        (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement α α inst inst A A f
          (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.fixElement α inst A f))
        (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.fixElement α inst A f))
    (∀ {α : Type u_1} {β : Type u_2} [inst : DecidableEq α] [inst_1 : DecidableEq β]
      (A : @DomainTheory.InformationSystems.InfoSys α inst) (B : @DomainTheory.InformationSystems.InfoSys β inst_1)
      (f : @DomainTheory.InformationSystems.InfoSys.ApproximableMap α α inst inst A A)
      (g : @DomainTheory.InformationSystems.InfoSys.ApproximableMap β β inst_1 inst_1 B B)
      (h : @DomainTheory.InformationSystems.InfoSys.ApproximableMap α β inst inst_1 A B),
      @Eq (@DomainTheory.InformationSystems.InfoSys.ApproximableMap α β inst inst_1 A B)
          (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.comp α α β inst inst inst_1 A A B h f)
          (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.comp α β β inst inst_1 inst_1 A B B g h) →
        @Eq (@DomainTheory.InformationSystems.InfoSys.Element β inst_1 B)
            (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement α β inst inst_1 A B h
              (@DomainTheory.InformationSystems.InfoSys.botElement α inst A))
            (@DomainTheory.InformationSystems.InfoSys.botElement β inst_1 B) →
          @Eq (@DomainTheory.InformationSystems.InfoSys.Element β inst_1 B)
            (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement α β inst inst_1 A B h
              (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.fixElement α inst A f))
            (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.fixElement β inst_1 B g))
    @DomainTheory.InformationSystems.InfoSys.ApproximableMap.proposition_7_4_ii
    @DomainTheory.InformationSystems.InfoSys.ApproximableMap.proposition_7_4_iii)
  @DomainTheory.InformationSystems.InfoSys.ApproximableMap.proposition_7_4_unique

end DomainTheory.InformationSystems.InfoSys.ApproximableMap

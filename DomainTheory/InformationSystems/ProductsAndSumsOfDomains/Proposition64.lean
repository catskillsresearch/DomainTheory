module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.copairMap_unique

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys.ApproximableMap

set_option linter.unusedVariables false

theorem theorem_64.{u_1, u_2, u_3} : ∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : DecidableEq α] [inst_1 : DecidableEq β] [inst_2 : DecidableEq γ]
  (A : @DomainTheory.InformationSystems.InfoSys α inst) (B : @DomainTheory.InformationSystems.InfoSys β inst_1)
  {C : @DomainTheory.InformationSystems.InfoSys γ inst_2}
  (f : @DomainTheory.InformationSystems.InfoSys.ApproximableMap α γ inst inst_2 A C)
  (g : @DomainTheory.InformationSystems.InfoSys.ApproximableMap β γ inst_1 inst_2 B C)
  (h :
    @DomainTheory.InformationSystems.InfoSys.ApproximableMap (DomainTheory.InformationSystems.InfoSys.SumToken α β) γ
      (fun (a b : DomainTheory.InformationSystems.InfoSys.SumToken α β) =>
        @DomainTheory.InformationSystems.InfoSys.instDecidableEqSumToken α β inst inst_1 a b)
      inst_2 (@DomainTheory.InformationSystems.InfoSys.sumSystem α β inst inst_1 A B) C),
  @Eq (@DomainTheory.InformationSystems.InfoSys.ApproximableMap α γ inst inst_2 A C)
      (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.comp α
        (DomainTheory.InformationSystems.InfoSys.SumToken α β) γ inst
        (fun (a b : DomainTheory.InformationSystems.InfoSys.SumToken α β) =>
          @DomainTheory.InformationSystems.InfoSys.instDecidableEqSumToken α β inst inst_1 a b)
        inst_2 A (@DomainTheory.InformationSystems.InfoSys.sumSystem α β inst inst_1 A B) C h
        (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.inlMap α β inst inst_1 A B))
      f →
    @Eq (@DomainTheory.InformationSystems.InfoSys.ApproximableMap β γ inst_1 inst_2 B C)
        (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.comp β
          (DomainTheory.InformationSystems.InfoSys.SumToken α β) γ inst_1
          (fun (a b : DomainTheory.InformationSystems.InfoSys.SumToken α β) =>
            @DomainTheory.InformationSystems.InfoSys.instDecidableEqSumToken α β inst inst_1 a b)
          inst_2 B (@DomainTheory.InformationSystems.InfoSys.sumSystem α β inst inst_1 A B) C h
          (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.inrMap α β inst inst_1 A B))
        g →
      @Eq (@DomainTheory.InformationSystems.InfoSys.Element γ inst_2 C)
          (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement
            (DomainTheory.InformationSystems.InfoSys.SumToken α β) γ
            (fun (a b : DomainTheory.InformationSystems.InfoSys.SumToken α β) =>
              @DomainTheory.InformationSystems.InfoSys.instDecidableEqSumToken α β inst inst_1 a b)
            inst_2 (@DomainTheory.InformationSystems.InfoSys.sumSystem α β inst inst_1 A B) C h
            (@DomainTheory.InformationSystems.InfoSys.botElement (DomainTheory.InformationSystems.InfoSys.SumToken α β)
              (fun (a b : DomainTheory.InformationSystems.InfoSys.SumToken α β) =>
                @DomainTheory.InformationSystems.InfoSys.instDecidableEqSumToken α β inst inst_1 a b)
              (@DomainTheory.InformationSystems.InfoSys.sumSystem α β inst inst_1 A B)))
          (@DomainTheory.InformationSystems.InfoSys.botElement γ inst_2 C) →
        @Eq
          (@DomainTheory.InformationSystems.InfoSys.ApproximableMap
            (DomainTheory.InformationSystems.InfoSys.SumToken α β) γ
            (fun (a b : DomainTheory.InformationSystems.InfoSys.SumToken α β) =>
              @DomainTheory.InformationSystems.InfoSys.instDecidableEqSumToken α β inst inst_1 a b)
            inst_2 (@DomainTheory.InformationSystems.InfoSys.sumSystem α β inst inst_1 A B) C)
          h (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.copairMap α β γ inst inst_1 inst_2 A B C f g) :=
  @DomainTheory.InformationSystems.InfoSys.ApproximableMap.copairMap_unique

end DomainTheory.InformationSystems.InfoSys.ApproximableMap

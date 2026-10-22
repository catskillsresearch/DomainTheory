module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.theorem_7_2
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.applyMap_toElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.curryMap_unique
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.uncurry_curryMap

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys

set_option linter.unusedVariables false

theorem theorem_72.{u, v, w} : And
  (And
    (And
      (∀ {α : Type u} {β : Type v} [inst : DecidableEq α] [inst_1 : DecidableEq β]
        (A : @DomainTheory.InformationSystems.InfoSys α inst) (B : @DomainTheory.InformationSystems.InfoSys β inst_1),
        And
          (∀ (f : @DomainTheory.InformationSystems.InfoSys.ApproximableMap α β inst inst_1 A B),
            @Eq (@DomainTheory.InformationSystems.InfoSys.ApproximableMap α β inst inst_1 A B)
              (@DomainTheory.InformationSystems.InfoSys.element_toApproxMap α β inst inst_1 A B
                (@DomainTheory.InformationSystems.InfoSys.approxMap_toElement α β inst inst_1 A B f))
              f)
          (∀
            (x :
              @DomainTheory.InformationSystems.InfoSys.Element
                (@DomainTheory.InformationSystems.InfoSys.FunToken α β inst inst_1 A B)
                (@DomainTheory.InformationSystems.InfoSys.instDecidableEqFunToken α β inst inst_1 A B)
                (@DomainTheory.InformationSystems.InfoSys.functionSystem α β inst inst_1 A B)),
            @Eq
              (@DomainTheory.InformationSystems.InfoSys.Element
                (@DomainTheory.InformationSystems.InfoSys.FunToken α β inst inst_1 A B)
                (@DomainTheory.InformationSystems.InfoSys.instDecidableEqFunToken α β inst inst_1 A B)
                (@DomainTheory.InformationSystems.InfoSys.functionSystem α β inst inst_1 A B))
              (@DomainTheory.InformationSystems.InfoSys.approxMap_toElement α β inst inst_1 A B
                (@DomainTheory.InformationSystems.InfoSys.element_toApproxMap α β inst inst_1 A B x))
              x))
      (∀ {β : Type v} {γ : Type w} [inst : DecidableEq β] [inst_1 : DecidableEq γ]
        (B : @DomainTheory.InformationSystems.InfoSys β inst) (C : @DomainTheory.InformationSystems.InfoSys γ inst_1)
        (g :
          @DomainTheory.InformationSystems.InfoSys.Element
            (@DomainTheory.InformationSystems.InfoSys.FunToken β γ inst inst_1 B C)
            (@DomainTheory.InformationSystems.InfoSys.instDecidableEqFunToken β γ inst inst_1 B C)
            (@DomainTheory.InformationSystems.InfoSys.functionSystem β γ inst inst_1 B C))
        (y : @DomainTheory.InformationSystems.InfoSys.Element β inst B),
        @Eq (@DomainTheory.InformationSystems.InfoSys.Element γ inst_1 C)
          (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement
            (@DomainTheory.InformationSystems.InfoSys.ProdToken
              (@DomainTheory.InformationSystems.InfoSys.FunToken β γ inst inst_1 B C) β
              (@DomainTheory.InformationSystems.InfoSys.instDecidableEqFunToken β γ inst inst_1 B C) inst
              (@DomainTheory.InformationSystems.InfoSys.functionSystem β γ inst inst_1 B C) B)
            γ
            (@DomainTheory.InformationSystems.InfoSys.instDecidableEqProdToken
              (@DomainTheory.InformationSystems.InfoSys.FunToken β γ inst inst_1 B C) β
              (@DomainTheory.InformationSystems.InfoSys.instDecidableEqFunToken β γ inst inst_1 B C) inst
              (@DomainTheory.InformationSystems.InfoSys.functionSystem β γ inst inst_1 B C) B)
            inst_1
            (@DomainTheory.InformationSystems.InfoSys.productSystem
              (@DomainTheory.InformationSystems.InfoSys.FunToken β γ inst inst_1 B C) β
              (@DomainTheory.InformationSystems.InfoSys.instDecidableEqFunToken β γ inst inst_1 B C) inst
              (@DomainTheory.InformationSystems.InfoSys.functionSystem β γ inst inst_1 B C) B)
            C (@DomainTheory.InformationSystems.InfoSys.applyMap β γ inst inst_1 B C)
            (@DomainTheory.InformationSystems.InfoSys.pairElements
              (@DomainTheory.InformationSystems.InfoSys.FunToken β γ inst inst_1 B C) β
              (@DomainTheory.InformationSystems.InfoSys.instDecidableEqFunToken β γ inst inst_1 B C) inst
              (@DomainTheory.InformationSystems.InfoSys.functionSystem β γ inst inst_1 B C) B g y))
          (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement β γ inst inst_1 B C
            (@DomainTheory.InformationSystems.InfoSys.element_toApproxMap β γ inst inst_1 B C g) y)))
    (∀ {α : Type u} {β : Type v} {γ : Type w} [inst : DecidableEq α] [inst_1 : DecidableEq β] [inst_2 : DecidableEq γ]
      (A : @DomainTheory.InformationSystems.InfoSys α inst) (B : @DomainTheory.InformationSystems.InfoSys β inst_1)
      (C : @DomainTheory.InformationSystems.InfoSys γ inst_2)
      (h :
        @DomainTheory.InformationSystems.InfoSys.ApproximableMap
          (@DomainTheory.InformationSystems.InfoSys.ProdToken α β inst inst_1 A B) γ
          (@DomainTheory.InformationSystems.InfoSys.instDecidableEqProdToken α β inst inst_1 A B) inst_2
          (@DomainTheory.InformationSystems.InfoSys.productSystem α β inst inst_1 A B) C)
      (k :
        @DomainTheory.InformationSystems.InfoSys.ApproximableMap α
          (@DomainTheory.InformationSystems.InfoSys.FunToken β γ inst_1 inst_2 B C) inst
          (@DomainTheory.InformationSystems.InfoSys.instDecidableEqFunToken β γ inst_1 inst_2 B C) A
          (@DomainTheory.InformationSystems.InfoSys.functionSystem β γ inst_1 inst_2 B C)),
      @Eq
          (@DomainTheory.InformationSystems.InfoSys.ApproximableMap
            (@DomainTheory.InformationSystems.InfoSys.ProdToken α β inst inst_1 A B) γ
            (@DomainTheory.InformationSystems.InfoSys.instDecidableEqProdToken α β inst inst_1 A B) inst_2
            (@DomainTheory.InformationSystems.InfoSys.productSystem α β inst inst_1 A B) C)
          (@DomainTheory.InformationSystems.InfoSys.uncurryMap α β γ inst inst_1 inst_2 A B C k) h →
        @Eq
          (@DomainTheory.InformationSystems.InfoSys.ApproximableMap α
            (@DomainTheory.InformationSystems.InfoSys.FunToken β γ inst_1 inst_2 B C) inst
            (@DomainTheory.InformationSystems.InfoSys.instDecidableEqFunToken β γ inst_1 inst_2 B C) A
            (@DomainTheory.InformationSystems.InfoSys.functionSystem β γ inst_1 inst_2 B C))
          k (@DomainTheory.InformationSystems.InfoSys.curryMap α β γ inst inst_1 inst_2 A B C h)))
  (∀ {α : Type u} {β : Type v} {γ : Type w} [inst : DecidableEq α] [inst_1 : DecidableEq β] [inst_2 : DecidableEq γ]
    (A : @DomainTheory.InformationSystems.InfoSys α inst) (B : @DomainTheory.InformationSystems.InfoSys β inst_1)
    (C : @DomainTheory.InformationSystems.InfoSys γ inst_2)
    (h :
      @DomainTheory.InformationSystems.InfoSys.ApproximableMap
        (@DomainTheory.InformationSystems.InfoSys.ProdToken α β inst inst_1 A B) γ
        (@DomainTheory.InformationSystems.InfoSys.instDecidableEqProdToken α β inst inst_1 A B) inst_2
        (@DomainTheory.InformationSystems.InfoSys.productSystem α β inst inst_1 A B) C),
    @Eq
      (@DomainTheory.InformationSystems.InfoSys.ApproximableMap
        (@DomainTheory.InformationSystems.InfoSys.ProdToken α β inst inst_1 A B) γ
        (@DomainTheory.InformationSystems.InfoSys.instDecidableEqProdToken α β inst inst_1 A B) inst_2
        (@DomainTheory.InformationSystems.InfoSys.productSystem α β inst inst_1 A B) C)
      (@DomainTheory.InformationSystems.InfoSys.uncurryMap α β γ inst inst_1 inst_2 A B C
        (@DomainTheory.InformationSystems.InfoSys.curryMap α β γ inst inst_1 inst_2 A B C h))
      h) :=
  @And.intro
  (And
    (And
      (∀ {α : Type u} {β : Type v} [inst : DecidableEq α] [inst_1 : DecidableEq β]
        (A : @DomainTheory.InformationSystems.InfoSys α inst) (B : @DomainTheory.InformationSystems.InfoSys β inst_1),
        And
          (∀ (f : @DomainTheory.InformationSystems.InfoSys.ApproximableMap α β inst inst_1 A B),
            @Eq (@DomainTheory.InformationSystems.InfoSys.ApproximableMap α β inst inst_1 A B)
              (@DomainTheory.InformationSystems.InfoSys.element_toApproxMap α β inst inst_1 A B
                (@DomainTheory.InformationSystems.InfoSys.approxMap_toElement α β inst inst_1 A B f))
              f)
          (∀
            (x :
              @DomainTheory.InformationSystems.InfoSys.Element
                (@DomainTheory.InformationSystems.InfoSys.FunToken α β inst inst_1 A B)
                (@DomainTheory.InformationSystems.InfoSys.instDecidableEqFunToken α β inst inst_1 A B)
                (@DomainTheory.InformationSystems.InfoSys.functionSystem α β inst inst_1 A B)),
            @Eq
              (@DomainTheory.InformationSystems.InfoSys.Element
                (@DomainTheory.InformationSystems.InfoSys.FunToken α β inst inst_1 A B)
                (@DomainTheory.InformationSystems.InfoSys.instDecidableEqFunToken α β inst inst_1 A B)
                (@DomainTheory.InformationSystems.InfoSys.functionSystem α β inst inst_1 A B))
              (@DomainTheory.InformationSystems.InfoSys.approxMap_toElement α β inst inst_1 A B
                (@DomainTheory.InformationSystems.InfoSys.element_toApproxMap α β inst inst_1 A B x))
              x))
      (∀ {β : Type v} {γ : Type w} [inst : DecidableEq β] [inst_1 : DecidableEq γ]
        (B : @DomainTheory.InformationSystems.InfoSys β inst) (C : @DomainTheory.InformationSystems.InfoSys γ inst_1)
        (g :
          @DomainTheory.InformationSystems.InfoSys.Element
            (@DomainTheory.InformationSystems.InfoSys.FunToken β γ inst inst_1 B C)
            (@DomainTheory.InformationSystems.InfoSys.instDecidableEqFunToken β γ inst inst_1 B C)
            (@DomainTheory.InformationSystems.InfoSys.functionSystem β γ inst inst_1 B C))
        (y : @DomainTheory.InformationSystems.InfoSys.Element β inst B),
        @Eq (@DomainTheory.InformationSystems.InfoSys.Element γ inst_1 C)
          (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement
            (@DomainTheory.InformationSystems.InfoSys.ProdToken
              (@DomainTheory.InformationSystems.InfoSys.FunToken β γ inst inst_1 B C) β
              (@DomainTheory.InformationSystems.InfoSys.instDecidableEqFunToken β γ inst inst_1 B C) inst
              (@DomainTheory.InformationSystems.InfoSys.functionSystem β γ inst inst_1 B C) B)
            γ
            (@DomainTheory.InformationSystems.InfoSys.instDecidableEqProdToken
              (@DomainTheory.InformationSystems.InfoSys.FunToken β γ inst inst_1 B C) β
              (@DomainTheory.InformationSystems.InfoSys.instDecidableEqFunToken β γ inst inst_1 B C) inst
              (@DomainTheory.InformationSystems.InfoSys.functionSystem β γ inst inst_1 B C) B)
            inst_1
            (@DomainTheory.InformationSystems.InfoSys.productSystem
              (@DomainTheory.InformationSystems.InfoSys.FunToken β γ inst inst_1 B C) β
              (@DomainTheory.InformationSystems.InfoSys.instDecidableEqFunToken β γ inst inst_1 B C) inst
              (@DomainTheory.InformationSystems.InfoSys.functionSystem β γ inst inst_1 B C) B)
            C (@DomainTheory.InformationSystems.InfoSys.applyMap β γ inst inst_1 B C)
            (@DomainTheory.InformationSystems.InfoSys.pairElements
              (@DomainTheory.InformationSystems.InfoSys.FunToken β γ inst inst_1 B C) β
              (@DomainTheory.InformationSystems.InfoSys.instDecidableEqFunToken β γ inst inst_1 B C) inst
              (@DomainTheory.InformationSystems.InfoSys.functionSystem β γ inst inst_1 B C) B g y))
          (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement β γ inst inst_1 B C
            (@DomainTheory.InformationSystems.InfoSys.element_toApproxMap β γ inst inst_1 B C g) y)))
    (∀ {α : Type u} {β : Type v} {γ : Type w} [inst : DecidableEq α] [inst_1 : DecidableEq β] [inst_2 : DecidableEq γ]
      (A : @DomainTheory.InformationSystems.InfoSys α inst) (B : @DomainTheory.InformationSystems.InfoSys β inst_1)
      (C : @DomainTheory.InformationSystems.InfoSys γ inst_2)
      (h :
        @DomainTheory.InformationSystems.InfoSys.ApproximableMap
          (@DomainTheory.InformationSystems.InfoSys.ProdToken α β inst inst_1 A B) γ
          (@DomainTheory.InformationSystems.InfoSys.instDecidableEqProdToken α β inst inst_1 A B) inst_2
          (@DomainTheory.InformationSystems.InfoSys.productSystem α β inst inst_1 A B) C)
      (k :
        @DomainTheory.InformationSystems.InfoSys.ApproximableMap α
          (@DomainTheory.InformationSystems.InfoSys.FunToken β γ inst_1 inst_2 B C) inst
          (@DomainTheory.InformationSystems.InfoSys.instDecidableEqFunToken β γ inst_1 inst_2 B C) A
          (@DomainTheory.InformationSystems.InfoSys.functionSystem β γ inst_1 inst_2 B C)),
      @Eq
          (@DomainTheory.InformationSystems.InfoSys.ApproximableMap
            (@DomainTheory.InformationSystems.InfoSys.ProdToken α β inst inst_1 A B) γ
            (@DomainTheory.InformationSystems.InfoSys.instDecidableEqProdToken α β inst inst_1 A B) inst_2
            (@DomainTheory.InformationSystems.InfoSys.productSystem α β inst inst_1 A B) C)
          (@DomainTheory.InformationSystems.InfoSys.uncurryMap α β γ inst inst_1 inst_2 A B C k) h →
        @Eq
          (@DomainTheory.InformationSystems.InfoSys.ApproximableMap α
            (@DomainTheory.InformationSystems.InfoSys.FunToken β γ inst_1 inst_2 B C) inst
            (@DomainTheory.InformationSystems.InfoSys.instDecidableEqFunToken β γ inst_1 inst_2 B C) A
            (@DomainTheory.InformationSystems.InfoSys.functionSystem β γ inst_1 inst_2 B C))
          k (@DomainTheory.InformationSystems.InfoSys.curryMap α β γ inst inst_1 inst_2 A B C h)))
  (∀ {α : Type u} {β : Type v} {γ : Type w} [inst : DecidableEq α] [inst_1 : DecidableEq β] [inst_2 : DecidableEq γ]
    (A : @DomainTheory.InformationSystems.InfoSys α inst) (B : @DomainTheory.InformationSystems.InfoSys β inst_1)
    (C : @DomainTheory.InformationSystems.InfoSys γ inst_2)
    (h :
      @DomainTheory.InformationSystems.InfoSys.ApproximableMap
        (@DomainTheory.InformationSystems.InfoSys.ProdToken α β inst inst_1 A B) γ
        (@DomainTheory.InformationSystems.InfoSys.instDecidableEqProdToken α β inst inst_1 A B) inst_2
        (@DomainTheory.InformationSystems.InfoSys.productSystem α β inst inst_1 A B) C),
    @Eq
      (@DomainTheory.InformationSystems.InfoSys.ApproximableMap
        (@DomainTheory.InformationSystems.InfoSys.ProdToken α β inst inst_1 A B) γ
        (@DomainTheory.InformationSystems.InfoSys.instDecidableEqProdToken α β inst inst_1 A B) inst_2
        (@DomainTheory.InformationSystems.InfoSys.productSystem α β inst inst_1 A B) C)
      (@DomainTheory.InformationSystems.InfoSys.uncurryMap α β γ inst inst_1 inst_2 A B C
        (@DomainTheory.InformationSystems.InfoSys.curryMap α β γ inst inst_1 inst_2 A B C h))
      h)
  (@And.intro
    (And
      (∀ {α : Type u} {β : Type v} [inst : DecidableEq α] [inst_1 : DecidableEq β]
        (A : @DomainTheory.InformationSystems.InfoSys α inst) (B : @DomainTheory.InformationSystems.InfoSys β inst_1),
        And
          (∀ (f : @DomainTheory.InformationSystems.InfoSys.ApproximableMap α β inst inst_1 A B),
            @Eq (@DomainTheory.InformationSystems.InfoSys.ApproximableMap α β inst inst_1 A B)
              (@DomainTheory.InformationSystems.InfoSys.element_toApproxMap α β inst inst_1 A B
                (@DomainTheory.InformationSystems.InfoSys.approxMap_toElement α β inst inst_1 A B f))
              f)
          (∀
            (x :
              @DomainTheory.InformationSystems.InfoSys.Element
                (@DomainTheory.InformationSystems.InfoSys.FunToken α β inst inst_1 A B)
                (@DomainTheory.InformationSystems.InfoSys.instDecidableEqFunToken α β inst inst_1 A B)
                (@DomainTheory.InformationSystems.InfoSys.functionSystem α β inst inst_1 A B)),
            @Eq
              (@DomainTheory.InformationSystems.InfoSys.Element
                (@DomainTheory.InformationSystems.InfoSys.FunToken α β inst inst_1 A B)
                (@DomainTheory.InformationSystems.InfoSys.instDecidableEqFunToken α β inst inst_1 A B)
                (@DomainTheory.InformationSystems.InfoSys.functionSystem α β inst inst_1 A B))
              (@DomainTheory.InformationSystems.InfoSys.approxMap_toElement α β inst inst_1 A B
                (@DomainTheory.InformationSystems.InfoSys.element_toApproxMap α β inst inst_1 A B x))
              x))
      (∀ {β : Type v} {γ : Type w} [inst : DecidableEq β] [inst_1 : DecidableEq γ]
        (B : @DomainTheory.InformationSystems.InfoSys β inst) (C : @DomainTheory.InformationSystems.InfoSys γ inst_1)
        (g :
          @DomainTheory.InformationSystems.InfoSys.Element
            (@DomainTheory.InformationSystems.InfoSys.FunToken β γ inst inst_1 B C)
            (@DomainTheory.InformationSystems.InfoSys.instDecidableEqFunToken β γ inst inst_1 B C)
            (@DomainTheory.InformationSystems.InfoSys.functionSystem β γ inst inst_1 B C))
        (y : @DomainTheory.InformationSystems.InfoSys.Element β inst B),
        @Eq (@DomainTheory.InformationSystems.InfoSys.Element γ inst_1 C)
          (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement
            (@DomainTheory.InformationSystems.InfoSys.ProdToken
              (@DomainTheory.InformationSystems.InfoSys.FunToken β γ inst inst_1 B C) β
              (@DomainTheory.InformationSystems.InfoSys.instDecidableEqFunToken β γ inst inst_1 B C) inst
              (@DomainTheory.InformationSystems.InfoSys.functionSystem β γ inst inst_1 B C) B)
            γ
            (@DomainTheory.InformationSystems.InfoSys.instDecidableEqProdToken
              (@DomainTheory.InformationSystems.InfoSys.FunToken β γ inst inst_1 B C) β
              (@DomainTheory.InformationSystems.InfoSys.instDecidableEqFunToken β γ inst inst_1 B C) inst
              (@DomainTheory.InformationSystems.InfoSys.functionSystem β γ inst inst_1 B C) B)
            inst_1
            (@DomainTheory.InformationSystems.InfoSys.productSystem
              (@DomainTheory.InformationSystems.InfoSys.FunToken β γ inst inst_1 B C) β
              (@DomainTheory.InformationSystems.InfoSys.instDecidableEqFunToken β γ inst inst_1 B C) inst
              (@DomainTheory.InformationSystems.InfoSys.functionSystem β γ inst inst_1 B C) B)
            C (@DomainTheory.InformationSystems.InfoSys.applyMap β γ inst inst_1 B C)
            (@DomainTheory.InformationSystems.InfoSys.pairElements
              (@DomainTheory.InformationSystems.InfoSys.FunToken β γ inst inst_1 B C) β
              (@DomainTheory.InformationSystems.InfoSys.instDecidableEqFunToken β γ inst inst_1 B C) inst
              (@DomainTheory.InformationSystems.InfoSys.functionSystem β γ inst inst_1 B C) B g y))
          (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement β γ inst inst_1 B C
            (@DomainTheory.InformationSystems.InfoSys.element_toApproxMap β γ inst inst_1 B C g) y)))
    (∀ {α : Type u} {β : Type v} {γ : Type w} [inst : DecidableEq α] [inst_1 : DecidableEq β] [inst_2 : DecidableEq γ]
      (A : @DomainTheory.InformationSystems.InfoSys α inst) (B : @DomainTheory.InformationSystems.InfoSys β inst_1)
      (C : @DomainTheory.InformationSystems.InfoSys γ inst_2)
      (h :
        @DomainTheory.InformationSystems.InfoSys.ApproximableMap
          (@DomainTheory.InformationSystems.InfoSys.ProdToken α β inst inst_1 A B) γ
          (@DomainTheory.InformationSystems.InfoSys.instDecidableEqProdToken α β inst inst_1 A B) inst_2
          (@DomainTheory.InformationSystems.InfoSys.productSystem α β inst inst_1 A B) C)
      (k :
        @DomainTheory.InformationSystems.InfoSys.ApproximableMap α
          (@DomainTheory.InformationSystems.InfoSys.FunToken β γ inst_1 inst_2 B C) inst
          (@DomainTheory.InformationSystems.InfoSys.instDecidableEqFunToken β γ inst_1 inst_2 B C) A
          (@DomainTheory.InformationSystems.InfoSys.functionSystem β γ inst_1 inst_2 B C)),
      @Eq
          (@DomainTheory.InformationSystems.InfoSys.ApproximableMap
            (@DomainTheory.InformationSystems.InfoSys.ProdToken α β inst inst_1 A B) γ
            (@DomainTheory.InformationSystems.InfoSys.instDecidableEqProdToken α β inst inst_1 A B) inst_2
            (@DomainTheory.InformationSystems.InfoSys.productSystem α β inst inst_1 A B) C)
          (@DomainTheory.InformationSystems.InfoSys.uncurryMap α β γ inst inst_1 inst_2 A B C k) h →
        @Eq
          (@DomainTheory.InformationSystems.InfoSys.ApproximableMap α
            (@DomainTheory.InformationSystems.InfoSys.FunToken β γ inst_1 inst_2 B C) inst
            (@DomainTheory.InformationSystems.InfoSys.instDecidableEqFunToken β γ inst_1 inst_2 B C) A
            (@DomainTheory.InformationSystems.InfoSys.functionSystem β γ inst_1 inst_2 B C))
          k (@DomainTheory.InformationSystems.InfoSys.curryMap α β γ inst inst_1 inst_2 A B C h))
    (@And.intro
      (∀ {α : Type u} {β : Type v} [inst : DecidableEq α] [inst_1 : DecidableEq β]
        (A : @DomainTheory.InformationSystems.InfoSys α inst) (B : @DomainTheory.InformationSystems.InfoSys β inst_1),
        And
          (∀ (f : @DomainTheory.InformationSystems.InfoSys.ApproximableMap α β inst inst_1 A B),
            @Eq (@DomainTheory.InformationSystems.InfoSys.ApproximableMap α β inst inst_1 A B)
              (@DomainTheory.InformationSystems.InfoSys.element_toApproxMap α β inst inst_1 A B
                (@DomainTheory.InformationSystems.InfoSys.approxMap_toElement α β inst inst_1 A B f))
              f)
          (∀
            (x :
              @DomainTheory.InformationSystems.InfoSys.Element
                (@DomainTheory.InformationSystems.InfoSys.FunToken α β inst inst_1 A B)
                (@DomainTheory.InformationSystems.InfoSys.instDecidableEqFunToken α β inst inst_1 A B)
                (@DomainTheory.InformationSystems.InfoSys.functionSystem α β inst inst_1 A B)),
            @Eq
              (@DomainTheory.InformationSystems.InfoSys.Element
                (@DomainTheory.InformationSystems.InfoSys.FunToken α β inst inst_1 A B)
                (@DomainTheory.InformationSystems.InfoSys.instDecidableEqFunToken α β inst inst_1 A B)
                (@DomainTheory.InformationSystems.InfoSys.functionSystem α β inst inst_1 A B))
              (@DomainTheory.InformationSystems.InfoSys.approxMap_toElement α β inst inst_1 A B
                (@DomainTheory.InformationSystems.InfoSys.element_toApproxMap α β inst inst_1 A B x))
              x))
      (∀ {β : Type v} {γ : Type w} [inst : DecidableEq β] [inst_1 : DecidableEq γ]
        (B : @DomainTheory.InformationSystems.InfoSys β inst) (C : @DomainTheory.InformationSystems.InfoSys γ inst_1)
        (g :
          @DomainTheory.InformationSystems.InfoSys.Element
            (@DomainTheory.InformationSystems.InfoSys.FunToken β γ inst inst_1 B C)
            (@DomainTheory.InformationSystems.InfoSys.instDecidableEqFunToken β γ inst inst_1 B C)
            (@DomainTheory.InformationSystems.InfoSys.functionSystem β γ inst inst_1 B C))
        (y : @DomainTheory.InformationSystems.InfoSys.Element β inst B),
        @Eq (@DomainTheory.InformationSystems.InfoSys.Element γ inst_1 C)
          (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement
            (@DomainTheory.InformationSystems.InfoSys.ProdToken
              (@DomainTheory.InformationSystems.InfoSys.FunToken β γ inst inst_1 B C) β
              (@DomainTheory.InformationSystems.InfoSys.instDecidableEqFunToken β γ inst inst_1 B C) inst
              (@DomainTheory.InformationSystems.InfoSys.functionSystem β γ inst inst_1 B C) B)
            γ
            (@DomainTheory.InformationSystems.InfoSys.instDecidableEqProdToken
              (@DomainTheory.InformationSystems.InfoSys.FunToken β γ inst inst_1 B C) β
              (@DomainTheory.InformationSystems.InfoSys.instDecidableEqFunToken β γ inst inst_1 B C) inst
              (@DomainTheory.InformationSystems.InfoSys.functionSystem β γ inst inst_1 B C) B)
            inst_1
            (@DomainTheory.InformationSystems.InfoSys.productSystem
              (@DomainTheory.InformationSystems.InfoSys.FunToken β γ inst inst_1 B C) β
              (@DomainTheory.InformationSystems.InfoSys.instDecidableEqFunToken β γ inst inst_1 B C) inst
              (@DomainTheory.InformationSystems.InfoSys.functionSystem β γ inst inst_1 B C) B)
            C (@DomainTheory.InformationSystems.InfoSys.applyMap β γ inst inst_1 B C)
            (@DomainTheory.InformationSystems.InfoSys.pairElements
              (@DomainTheory.InformationSystems.InfoSys.FunToken β γ inst inst_1 B C) β
              (@DomainTheory.InformationSystems.InfoSys.instDecidableEqFunToken β γ inst inst_1 B C) inst
              (@DomainTheory.InformationSystems.InfoSys.functionSystem β γ inst inst_1 B C) B g y))
          (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement β γ inst inst_1 B C
            (@DomainTheory.InformationSystems.InfoSys.element_toApproxMap β γ inst inst_1 B C g) y))
      @DomainTheory.InformationSystems.InfoSys.theorem_7_2 @DomainTheory.InformationSystems.InfoSys.applyMap_toElement)
    @DomainTheory.InformationSystems.InfoSys.curryMap_unique)
  @DomainTheory.InformationSystems.InfoSys.uncurry_curryMap

end DomainTheory.InformationSystems.InfoSys

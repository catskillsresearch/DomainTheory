module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.copairMap

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys.ApproximableMap

theorem proposition_6_4 :
    ∀ {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
      (A : InfoSys α) (B : InfoSys β) {C : InfoSys γ}
      (f : ApproximableMap A C) (g : ApproximableMap B C)
      (h : ApproximableMap (sumSystem A B) C),
      comp h (inlMap A B) = f →
        comp h (inrMap A B) = g →
          h.toElement (sumSystem A B).botElement = C.botElement →
            h = copairMap A B f g :=
  @copairMap.unique

end DomainTheory.InformationSystems.InfoSys.ApproximableMap

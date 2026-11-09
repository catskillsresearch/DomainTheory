module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.productSystem
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.pairMap

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys.ApproximableMap

theorem proposition_6_2 :
    ∀ {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
      (A : InfoSys α) (B : InfoSys β) {C : InfoSys γ}
      (f : ApproximableMap C A) (g : ApproximableMap C B)
      (h : ApproximableMap C (productSystem A B)),
      comp (productSystem.fstMap A B) h = f →
        comp (productSystem.sndMap A B) h = g →
          h = pairMap A B f g :=
  @pairMap.unique

end DomainTheory.InformationSystems.InfoSys.ApproximableMap

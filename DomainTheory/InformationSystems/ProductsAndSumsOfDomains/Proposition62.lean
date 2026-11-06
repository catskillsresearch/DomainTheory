module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.pairMap_unique

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys.ApproximableMap

theorem theorem_62 :
    ∀ {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
      (A : InfoSys α) (B : InfoSys β) {C : InfoSys γ}
      (f : ApproximableMap C A) (g : ApproximableMap C B)
      (h : ApproximableMap C (productSystem A B)),
      comp (fstMap A B) h = f →
        comp (sndMap A B) h = g →
          h = pairMap A B f g :=
  @pairMap_unique

end DomainTheory.InformationSystems.InfoSys.ApproximableMap

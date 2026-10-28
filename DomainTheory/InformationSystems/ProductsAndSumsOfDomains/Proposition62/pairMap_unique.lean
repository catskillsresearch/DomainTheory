module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.Basic
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.element_eq_of_fst_snd
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.comp_fstMap_pairMap
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.comp_sndMap_pairMap

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β)

namespace ApproximableMap

variable {C : InfoSys γ}

theorem pairMap_unique (f : ApproximableMap C A) (g : ApproximableMap C B)
    (h : ApproximableMap C (productSystem A B))
    (hfst : comp (fstMap A B) h = f) (hsnd : comp (sndMap A B) h = g) :
    h = pairMap A B f g :=
  (ext_iff_toElement h (pairMap A B f g)).2 fun x =>
    element_eq_of_fst_snd A B (h.toElement x) ((pairMap A B f g).toElement x)
      (by
        have h1 : (fstMap A B).toElement (h.toElement x) = f.toElement x := by
          rw [← comp.toElement, hfst]
        have h2 : (fstMap A B).toElement ((pairMap A B f g).toElement x) = f.toElement x := by
          rw [← comp.toElement, comp_fstMap_pairMap]
        exact h1.trans h2.symm)
      (by
        have h1 : (sndMap A B).toElement (h.toElement x) = g.toElement x := by
          rw [← comp.toElement, hsnd]
        have h2 : (sndMap A B).toElement ((pairMap A B f g).toElement x) = g.toElement x := by
          rw [← comp.toElement, comp_sndMap_pairMap]
        exact h1.trans h2.symm)

end ApproximableMap
end InfoSys

end DomainTheory.InformationSystems

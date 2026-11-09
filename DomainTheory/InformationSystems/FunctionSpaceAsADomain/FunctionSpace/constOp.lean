module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.productSystem
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.theorem_7_2
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition56
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition56.constMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.applyMap_toElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.fstMap_pairElements
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.sndMap_pairElements
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.uncurry_curryMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.approxMap_toElement_element_toApproxMap

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

open ApproximableMap
variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

def constOp : ApproximableMap B (functionSystem A B) :=
  curryMap B A B (productSystem.fstMap B A)

theorem constOp.uncurry : uncurryMap B A B (constOp A B) = productSystem.fstMap B A := by
  simp only [constOp, uncurry_curryMap]

theorem pairMap_comp_fst_snd_toElement
    {P : InfoSys α} {X : InfoSys β} {Y : InfoSys γ}
    (k : ApproximableMap P (functionSystem Y X))
    (p : P.Element) (y : Y.Element) :
    (pairMap (functionSystem Y X) Y (comp k (productSystem.fstMap P Y)) (productSystem.sndMap P Y)).toElement
      (pairElements P Y p y) =
      pairElements (functionSystem Y X) Y (k.toElement p) y := by
  refine productSystem.element_eq_of_fst_snd (functionSystem Y X) Y _ _ ?_ ?_
  · rw [← comp.toElement, pairMap.comp_fst, comp.toElement, fstMap_pairElements,
      fstMap_pairElements]
  · rw [← comp.toElement, pairMap.comp_snd, sndMap_pairElements, sndMap_pairElements]

theorem constOp.toElement (b : B.Element) :
    (constOp A B).toElement b =
      approxMap_toElement A B (constMap (A := A) b) := by
  have huniq :
      element_toApproxMap A B ((constOp A B).toElement b) = constMap (A := A) b := by
    refine constMap.unique (A := A) b _ fun x => ?_
    have hpair := pairMap_comp_fst_snd_toElement (constOp A B) b x
    calc
      (element_toApproxMap A B ((constOp A B).toElement b)).toElement x
          = (uncurryMap B A B (constOp A B)).toElement (pairElements B A b x) := by
              simp only [uncurryMap, comp.toElement]
              rw [hpair, applyMap_toElement]
          _ = (productSystem.fstMap B A).toElement (pairElements B A b x) := by rw [constOp.uncurry]
          _ = b := fstMap_pairElements B A b x
  rw [← huniq, approxMap_toElement_element_toApproxMap]

end InfoSys

end DomainTheory.InformationSystems

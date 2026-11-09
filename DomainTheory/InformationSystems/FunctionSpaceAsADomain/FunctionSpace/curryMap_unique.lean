module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.curryMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.uncurryMap
import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.uncurry_curryMap
import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.applyMap_toElement
import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.sndMap_pairElements
import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.fstMap_pairElements
import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.approxMap_toElement_element_toApproxMap
import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.productSystem_more

@[expose] public section

namespace DomainTheory.InformationSystems

namespace InfoSys

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

open ApproximableMap

theorem curryMap_unique (h : ApproximableMap (productSystem A B) C)
    (k : ApproximableMap A (functionSystem B C))
    (huniv : uncurryMap A B C k = h) :
    k = curryMap A B C h := by
  have hk : uncurryMap A B C k = uncurryMap A B C (curryMap A B C h) := by
    rw [huniv, uncurry_curryMap]
  refine (ext_iff_toElement k (curryMap A B C h)).2 fun x => ?_
  have happly : ∀ y : B.Element,
      (element_toApproxMap B C (k.toElement x)).toElement y =
        (element_toApproxMap B C ((curryMap A B C h).toElement x)).toElement y := by
    intro y
    have hpair_k :
        (pairMap (functionSystem B C) B (comp k (productSystem.fstMap A B)) (productSystem.sndMap A B)).toElement
          (pairElements A B x y) =
        pairElements (functionSystem B C) B (k.toElement x) y := by
      apply productSystem.element_eq_of_fst_snd (functionSystem B C) B
      · have h1 : (productSystem.fstMap (functionSystem B C) B).toElement
            ((pairMap (functionSystem B C) B (comp k (productSystem.fstMap A B)) (productSystem.sndMap A B)).toElement
              (pairElements A B x y)) = k.toElement x := by
          rw [← comp.toElement, pairMap.comp_fst, comp.toElement, fstMap_pairElements]
        exact h1.trans (fstMap_pairElements (functionSystem B C) B (k.toElement x) y).symm
      · have h1 : (productSystem.sndMap (functionSystem B C) B).toElement
            ((pairMap (functionSystem B C) B (comp k (productSystem.fstMap A B)) (productSystem.sndMap A B)).toElement
              (pairElements A B x y)) = y := by
          rw [← comp.toElement, pairMap.comp_snd, sndMap_pairElements]
        exact h1.trans (sndMap_pairElements (functionSystem B C) B (k.toElement x) y).symm
    have hpair_c :
        (pairMap (functionSystem B C) B
            (comp (curryMap A B C h) (productSystem.fstMap A B)) (productSystem.sndMap A B)).toElement
          (pairElements A B x y) =
        pairElements (functionSystem B C) B ((curryMap A B C h).toElement x) y := by
      apply productSystem.element_eq_of_fst_snd (functionSystem B C) B
      · have h1 : (productSystem.fstMap (functionSystem B C) B).toElement
            ((pairMap (functionSystem B C) B
                (comp (curryMap A B C h) (productSystem.fstMap A B)) (productSystem.sndMap A B)).toElement
              (pairElements A B x y)) = (curryMap A B C h).toElement x := by
          rw [← comp.toElement, pairMap.comp_fst, comp.toElement, fstMap_pairElements]
        exact h1.trans
          (fstMap_pairElements (functionSystem B C) B ((curryMap A B C h).toElement x) y).symm
      · have h1 : (productSystem.sndMap (functionSystem B C) B).toElement
            ((pairMap (functionSystem B C) B
                (comp (curryMap A B C h) (productSystem.fstMap A B)) (productSystem.sndMap A B)).toElement
              (pairElements A B x y)) = y := by
          rw [← comp.toElement, pairMap.comp_snd, sndMap_pairElements]
        exact h1.trans
          (sndMap_pairElements (functionSystem B C) B ((curryMap A B C h).toElement x) y).symm
    have hu1 : (uncurryMap A B C k).toElement (pairElements A B x y) =
        (applyMap (B := B) (C := C)).toElement
          (pairElements (functionSystem B C) B (k.toElement x) y) := by
      simp only [uncurryMap, comp.toElement, hpair_k]
    have hu2 : (uncurryMap A B C (curryMap A B C h)).toElement (pairElements A B x y) =
        (applyMap (B := B) (C := C)).toElement
          (pairElements (functionSystem B C) B ((curryMap A B C h).toElement x) y) := by
      simp only [uncurryMap, comp.toElement, hpair_c]
    have heq : (uncurryMap A B C k).toElement (pairElements A B x y) =
        (uncurryMap A B C (curryMap A B C h)).toElement (pairElements A B x y) := by
      rw [hk]
    rw [← applyMap_toElement, ← applyMap_toElement, ← hu1, ← hu2, heq]
  have hx : element_toApproxMap B C (k.toElement x) =
      element_toApproxMap B C ((curryMap A B C h).toElement x) :=
    (ext_iff_toElement _ _).2 happly
  have : k.toElement x = (curryMap A B C h).toElement x := by
    rw [← approxMap_toElement_element_toApproxMap B C (k.toElement x),
      ← approxMap_toElement_element_toApproxMap B C ((curryMap A B C h).toElement x), hx]
  rw [this]

end InfoSys
end DomainTheory.InformationSystems

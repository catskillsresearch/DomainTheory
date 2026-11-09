module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.productSystem
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.theorem_7_2
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition56
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.curryMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.pairElements

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

open ApproximableMap
variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

def pairOpUncurry : ApproximableMap
    (productSystem (productSystem (functionSystem C A) (functionSystem C B)) C)
    (productSystem A B) :=
  let P := productSystem (functionSystem C A) (functionSystem C B)
  pairMap A B
    (comp (applyMap (B := C) (C := A))
      (pairMap (functionSystem C A) C
        (comp (productSystem.fstMap (functionSystem C A) (functionSystem C B)) (productSystem.fstMap P C))
        (productSystem.sndMap P C)))
    (comp (applyMap (B := C) (C := B))
      (pairMap (functionSystem C B) C
        (comp (productSystem.sndMap (functionSystem C A) (functionSystem C B)) (productSystem.fstMap P C))
        (productSystem.sndMap P C)))

theorem pairOpUncurry.toElement (f : ApproximableMap C A) (g : ApproximableMap C B)
    (x : C.Element) :
    (pairOpUncurry A B C).toElement
      (pairElements (productSystem (functionSystem C A) (functionSystem C B)) C
        (pairElements (functionSystem C A) (functionSystem C B)
          (approxMap_toElement C A f) (approxMap_toElement C B g))
        x) =
      (pairMap A B f g).toElement x := by
  let P := productSystem (functionSystem C A) (functionSystem C B)
  let fg := pairElements (functionSystem C A) (functionSystem C B)
      (approxMap_toElement C A f) (approxMap_toElement C B g)
  have hfst_arg :
      (pairMap (functionSystem C A) C
          (comp (productSystem.fstMap (functionSystem C A) (functionSystem C B)) (productSystem.fstMap P C))
          (productSystem.sndMap P C)).toElement
        (pairElements P C fg x) =
      pairElements (functionSystem C A) C (approxMap_toElement C A f) x := by
    refine productSystem.element_eq_of_fst_snd (functionSystem C A) C _ _ ?_ ?_
    · have hL :
          (productSystem.fstMap (functionSystem C A) C).toElement
            ((pairMap (functionSystem C A) C
                (comp (productSystem.fstMap (functionSystem C A) (functionSystem C B)) (productSystem.fstMap P C))
                (productSystem.sndMap P C)).toElement
              (pairElements P C fg x)) =
          approxMap_toElement C A f := by
        rw [← comp.toElement, pairMap.comp_fst, comp.toElement, fstMap_pairElements,
          fstMap_pairElements]
      exact hL.trans (fstMap_pairElements (functionSystem C A) C _ _).symm
    · have hL :
          (productSystem.sndMap (functionSystem C A) C).toElement
            ((pairMap (functionSystem C A) C
                (comp (productSystem.fstMap (functionSystem C A) (functionSystem C B)) (productSystem.fstMap P C))
                (productSystem.sndMap P C)).toElement
              (pairElements P C fg x)) =
          x := by
        rw [← comp.toElement, pairMap.comp_snd, sndMap_pairElements]
      exact hL.trans (sndMap_pairElements (functionSystem C A) C _ _).symm
  have hsnd_arg :
      (pairMap (functionSystem C B) C
          (comp (productSystem.sndMap (functionSystem C A) (functionSystem C B)) (productSystem.fstMap P C))
          (productSystem.sndMap P C)).toElement
        (pairElements P C fg x) =
      pairElements (functionSystem C B) C (approxMap_toElement C B g) x := by
    refine productSystem.element_eq_of_fst_snd (functionSystem C B) C _ _ ?_ ?_
    · have hL :
          (productSystem.fstMap (functionSystem C B) C).toElement
            ((pairMap (functionSystem C B) C
                (comp (productSystem.sndMap (functionSystem C A) (functionSystem C B)) (productSystem.fstMap P C))
                (productSystem.sndMap P C)).toElement
              (pairElements P C fg x)) =
          approxMap_toElement C B g := by
        rw [← comp.toElement, pairMap.comp_fst, comp.toElement, fstMap_pairElements,
          sndMap_pairElements]
      exact hL.trans (fstMap_pairElements (functionSystem C B) C _ _).symm
    · have hL :
          (productSystem.sndMap (functionSystem C B) C).toElement
            ((pairMap (functionSystem C B) C
                (comp (productSystem.sndMap (functionSystem C A) (functionSystem C B)) (productSystem.fstMap P C))
                (productSystem.sndMap P C)).toElement
              (pairElements P C fg x)) =
          x := by
        rw [← comp.toElement, pairMap.comp_snd, sndMap_pairElements]
      exact hL.trans (sndMap_pairElements (functionSystem C B) C _ _).symm
  refine productSystem.element_eq_of_fst_snd A B _ _ ?_ ?_
  · have L :
        (productSystem.fstMap A B).toElement
          ((pairOpUncurry A B C).toElement (pairElements P C fg x)) =
        f.toElement x := by
      simp only [pairOpUncurry]
      rw [← comp.toElement, pairMap.comp_fst, comp.toElement, hfst_arg,
        applyMap_toElement, element_toApproxMap.approxMap_toElement]
    have R :
        (productSystem.fstMap A B).toElement ((pairMap A B f g).toElement x) = f.toElement x := by
      rw [← comp.toElement, pairMap.comp_fst]
    exact L.trans R.symm
  · have L :
        (productSystem.sndMap A B).toElement
          ((pairOpUncurry A B C).toElement (pairElements P C fg x)) =
        g.toElement x := by
      simp only [pairOpUncurry]
      rw [← comp.toElement, pairMap.comp_snd, comp.toElement, hsnd_arg,
        applyMap_toElement, element_toApproxMap.approxMap_toElement]
    have R :
        (productSystem.sndMap A B).toElement ((pairMap A B f g).toElement x) = g.toElement x := by
      rw [← comp.toElement, pairMap.comp_snd]
    exact L.trans R.symm

end InfoSys

end DomainTheory.InformationSystems

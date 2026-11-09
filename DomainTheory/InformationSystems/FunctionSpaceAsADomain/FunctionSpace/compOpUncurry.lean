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

def compOpUncurry : ApproximableMap
    (productSystem (productSystem (functionSystem B C) (functionSystem A B)) A) C :=
  let Q := productSystem (functionSystem B C) (functionSystem A B)
  comp (applyMap (B := B) (C := C))
    (pairMap (functionSystem B C) B
      (comp (productSystem.fstMap (functionSystem B C) (functionSystem A B)) (productSystem.fstMap Q A))
      (comp (applyMap (B := A) (C := B))
        (pairMap (functionSystem A B) A
          (comp (productSystem.sndMap (functionSystem B C) (functionSystem A B)) (productSystem.fstMap Q A))
          (productSystem.sndMap Q A))))

theorem compOpUncurry.toElement (g : ApproximableMap B C) (f : ApproximableMap A B)
    (x : A.Element) :
    (compOpUncurry A B C).toElement
      (pairElements (productSystem (functionSystem B C) (functionSystem A B)) A
        (pairElements (functionSystem B C) (functionSystem A B)
          (approxMap_toElement B C g) (approxMap_toElement A B f))
        x) =
      (comp g f).toElement x := by
  let Q := productSystem (functionSystem B C) (functionSystem A B)
  let gf := pairElements (functionSystem B C) (functionSystem A B)
      (approxMap_toElement B C g) (approxMap_toElement A B f)
  have hinner :
      (pairMap (functionSystem A B) A
          (comp (productSystem.sndMap (functionSystem B C) (functionSystem A B)) (productSystem.fstMap Q A))
          (productSystem.sndMap Q A)).toElement
        (pairElements Q A gf x) =
      pairElements (functionSystem A B) A (approxMap_toElement A B f) x := by
    refine productSystem.element_eq_of_fst_snd (functionSystem A B) A _ _ ?_ ?_
    · have hL :
          (productSystem.fstMap (functionSystem A B) A).toElement
            ((pairMap (functionSystem A B) A
                (comp (productSystem.sndMap (functionSystem B C) (functionSystem A B)) (productSystem.fstMap Q A))
                (productSystem.sndMap Q A)).toElement
              (pairElements Q A gf x)) =
          approxMap_toElement A B f := by
        rw [← comp.toElement, pairMap.comp_fst, comp.toElement, fstMap_pairElements,
          sndMap_pairElements]
      exact hL.trans (fstMap_pairElements (functionSystem A B) A _ _).symm
    · have hL :
          (productSystem.sndMap (functionSystem A B) A).toElement
            ((pairMap (functionSystem A B) A
                (comp (productSystem.sndMap (functionSystem B C) (functionSystem A B)) (productSystem.fstMap Q A))
                (productSystem.sndMap Q A)).toElement
              (pairElements Q A gf x)) =
          x := by
        rw [← comp.toElement, pairMap.comp_snd, sndMap_pairElements]
      exact hL.trans (sndMap_pairElements (functionSystem A B) A _ _).symm
  have hf :
      (comp (applyMap (B := A) (C := B))
        (pairMap (functionSystem A B) A
          (comp (productSystem.sndMap (functionSystem B C) (functionSystem A B)) (productSystem.fstMap Q A))
          (productSystem.sndMap Q A))).toElement
        (pairElements Q A gf x) =
      f.toElement x := by
    rw [comp.toElement, hinner, applyMap_toElement, element_toApproxMap.approxMap_toElement]
  have houter :
      (pairMap (functionSystem B C) B
          (comp (productSystem.fstMap (functionSystem B C) (functionSystem A B)) (productSystem.fstMap Q A))
          (comp (applyMap (B := A) (C := B))
            (pairMap (functionSystem A B) A
              (comp (productSystem.sndMap (functionSystem B C) (functionSystem A B)) (productSystem.fstMap Q A))
              (productSystem.sndMap Q A)))).toElement
        (pairElements Q A gf x) =
      pairElements (functionSystem B C) B (approxMap_toElement B C g) (f.toElement x) := by
    refine productSystem.element_eq_of_fst_snd (functionSystem B C) B _ _ ?_ ?_
    · have hL :
          (productSystem.fstMap (functionSystem B C) B).toElement
            ((pairMap (functionSystem B C) B
                (comp (productSystem.fstMap (functionSystem B C) (functionSystem A B)) (productSystem.fstMap Q A))
                (comp (applyMap (B := A) (C := B))
                  (pairMap (functionSystem A B) A
                    (comp (productSystem.sndMap (functionSystem B C) (functionSystem A B)) (productSystem.fstMap Q A))
                    (productSystem.sndMap Q A)))).toElement
              (pairElements Q A gf x)) =
          approxMap_toElement B C g := by
        rw [← comp.toElement, pairMap.comp_fst, comp.toElement, fstMap_pairElements,
          fstMap_pairElements]
      exact hL.trans (fstMap_pairElements (functionSystem B C) B _ _).symm
    · have hL :
          (productSystem.sndMap (functionSystem B C) B).toElement
            ((pairMap (functionSystem B C) B
                (comp (productSystem.fstMap (functionSystem B C) (functionSystem A B)) (productSystem.fstMap Q A))
                (comp (applyMap (B := A) (C := B))
                  (pairMap (functionSystem A B) A
                    (comp (productSystem.sndMap (functionSystem B C) (functionSystem A B)) (productSystem.fstMap Q A))
                    (productSystem.sndMap Q A)))).toElement
              (pairElements Q A gf x)) =
          f.toElement x := by
        rw [← comp.toElement, pairMap.comp_snd, hf]
      exact hL.trans (sndMap_pairElements (functionSystem B C) B _ _).symm
  simp only [compOpUncurry, comp.toElement]
  rw [houter, applyMap_toElement, element_toApproxMap.approxMap_toElement]

end InfoSys

end DomainTheory.InformationSystems

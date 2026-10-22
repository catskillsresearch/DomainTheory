module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition56
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid76.Basic

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.applyMap_toElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.fstMap_pairElements
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.sndMap_pairElements
@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

open ApproximableMap

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)


theorem pairOpUncurry_toElement (f : ApproximableMap C A) (g : ApproximableMap C B)
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
          (comp (fstMap (functionSystem C A) (functionSystem C B)) (fstMap P C))
          (sndMap P C)).toElement
        (pairElements P C fg x) =
      pairElements (functionSystem C A) C (approxMap_toElement C A f) x := by
    refine element_eq_of_fst_snd (functionSystem C A) C _ _ ?_ ?_
    · have hL :
          (fstMap (functionSystem C A) C).toElement
            ((pairMap (functionSystem C A) C
                (comp (fstMap (functionSystem C A) (functionSystem C B)) (fstMap P C))
                (sndMap P C)).toElement
              (pairElements P C fg x)) =
          approxMap_toElement C A f := by
        rw [← comp_toElement, comp_fstMap_pairMap, comp_toElement, fstMap_pairElements,
          fstMap_pairElements]
      exact hL.trans (fstMap_pairElements (functionSystem C A) C _ _).symm
    · have hL :
          (sndMap (functionSystem C A) C).toElement
            ((pairMap (functionSystem C A) C
                (comp (fstMap (functionSystem C A) (functionSystem C B)) (fstMap P C))
                (sndMap P C)).toElement
              (pairElements P C fg x)) =
          x := by
        rw [← comp_toElement, comp_sndMap_pairMap, sndMap_pairElements]
      exact hL.trans (sndMap_pairElements (functionSystem C A) C _ _).symm
  have hsnd_arg :
      (pairMap (functionSystem C B) C
          (comp (sndMap (functionSystem C A) (functionSystem C B)) (fstMap P C))
          (sndMap P C)).toElement
        (pairElements P C fg x) =
      pairElements (functionSystem C B) C (approxMap_toElement C B g) x := by
    refine element_eq_of_fst_snd (functionSystem C B) C _ _ ?_ ?_
    · have hL :
          (fstMap (functionSystem C B) C).toElement
            ((pairMap (functionSystem C B) C
                (comp (sndMap (functionSystem C A) (functionSystem C B)) (fstMap P C))
                (sndMap P C)).toElement
              (pairElements P C fg x)) =
          approxMap_toElement C B g := by
        rw [← comp_toElement, comp_fstMap_pairMap, comp_toElement, fstMap_pairElements,
          sndMap_pairElements]
      exact hL.trans (fstMap_pairElements (functionSystem C B) C _ _).symm
    · have hL :
          (sndMap (functionSystem C B) C).toElement
            ((pairMap (functionSystem C B) C
                (comp (sndMap (functionSystem C A) (functionSystem C B)) (fstMap P C))
                (sndMap P C)).toElement
              (pairElements P C fg x)) =
          x := by
        rw [← comp_toElement, comp_sndMap_pairMap, sndMap_pairElements]
      exact hL.trans (sndMap_pairElements (functionSystem C B) C _ _).symm
  refine element_eq_of_fst_snd A B _ _ ?_ ?_
  · have L :
        (fstMap A B).toElement
          ((pairOpUncurry A B C).toElement (pairElements P C fg x)) =
        f.toElement x := by
      simp only [pairOpUncurry]
      rw [← comp_toElement, comp_fstMap_pairMap, comp_toElement, hfst_arg,
        applyMap_toElement, element_toApproxMap_approxMap_toElement]
    have R :
        (fstMap A B).toElement ((pairMap A B f g).toElement x) = f.toElement x := by
      rw [← comp_toElement, comp_fstMap_pairMap]
    exact L.trans R.symm
  · have L :
        (sndMap A B).toElement
          ((pairOpUncurry A B C).toElement (pairElements P C fg x)) =
        g.toElement x := by
      simp only [pairOpUncurry]
      rw [← comp_toElement, comp_sndMap_pairMap, comp_toElement, hsnd_arg,
        applyMap_toElement, element_toApproxMap_approxMap_toElement]
    have R :
        (sndMap A B).toElement ((pairMap A B f g).toElement x) = g.toElement x := by
      rw [← comp_toElement, comp_sndMap_pairMap]
    exact L.trans R.symm

end InfoSys
end DomainTheory.InformationSystems

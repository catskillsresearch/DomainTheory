
module

public import DomainTheory.DataTypesAsLattices.Retracts.comp
public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.typed
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR
public import DomainTheory.DataTypesAsLattices.Retracts.fstC
public import DomainTheory.DataTypesAsLattices.Retracts.sndC
public import DomainTheory.DataTypesAsLattices.Retracts.pairSeq
public import DomainTheory.DataTypesAsLattices.Retracts.tensorR
public import DomainTheory.DataTypesAsLattices.Retracts.diagC
public import DomainTheory.DataTypesAsLattices.Retracts.retract_app
public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.pairMed
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_zero
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_one
public import DomainTheory.DataTypesAsLattices.Functionality.tensorR_app
public import DomainTheory.DataTypesAsLattices.Functionality.diagC_app
public import DomainTheory.DataTypesAsLattices.Functionality.graph_funOf_ext
public import DomainTheory.DataTypesAsLattices.Functionality.typed_isGraph
public import DomainTheory.DataTypesAsLattices.Functionality.comp_isGraph
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR_more
public import DomainTheory.DataTypesAsLattices.Retracts.typed_more

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem theorem_4_4_med {a b c f g : Pomega}
    (_ha : Retract a) (_hb : Retract b) (hc : Retract c)
    (hf : typed f (arrowR c a)) (hg : typed g (arrowR c b)) :
    typed (pairMed f g c) (arrowR c (tensorR a b)) ∧
      comp fstC (pairMed f g c) = f ∧
      comp sndC (pairMed f g c) = g := by
  have hf' := arrowR.typed_of hf
  have hg' := arrowR.typed_of hg
  refine ⟨?_, ?_, ?_⟩
  · change pairMed f g c =
        funOf (arrowR c (tensorR a b)) (pairMed f g c)
    rw [arrowR.app, pairMed]
    apply graph_ext
    intro x
    have hfxc : funOf f (funOf c x) =
        funOf a (funOf f (funOf c x)) := by
      have := congrArg (fun w => funOf w (funOf c x)) hf'
      simpa [comp.app, retract_app hc] using this
    have hgxc : funOf g (funOf c x) =
        funOf b (funOf g (funOf c x)) := by
      have := congrArg (fun w => funOf w (funOf c x)) hg'
      simpa [comp.app, retract_app hc] using this
    have hL : funOf (tensorR f g) (funOf diagC (funOf c x)) =
        pairSeq (funOf f (funOf c x)) (funOf g (funOf c x)) := by
      rw [diagC_app, tensorR_app, pairSeq_app_zero, pairSeq_app_one]
    have hR : funOf (tensorR a b)
        (funOf (tensorR f g) (funOf diagC (funOf c (funOf c x)))) =
        pairSeq (funOf a (funOf f (funOf c x)))
          (funOf b (funOf g (funOf c x))) := by
      rw [retract_app hc, diagC_app]
      have hinter :
          funOf (tensorR f g) (pairSeq (funOf c x) (funOf c x)) =
            pairSeq (funOf f (funOf c x)) (funOf g (funOf c x)) := by
        rw [tensorR_app, pairSeq_app_zero, pairSeq_app_one]
      rw [hinter, tensorR_app, pairSeq_app_zero, pairSeq_app_one]
    simp only [comp.app]
    rw [hL, hR]
    exact congr (congrArg pairSeq hfxc) hgxc
  · apply graph_funOf_ext (comp_isGraph _ _) (typed_isGraph hf)
    intro x
    simp only [comp.app, pairMed, fstC.app, diagC_app]
    rw [tensorR_app, pairSeq_app_zero, pairSeq_app_zero]
    have := congrArg (fun w => funOf w x) (typed.arrowR_restrict hc hf)
    simpa [comp.app] using this.symm
  · apply graph_funOf_ext (comp_isGraph _ _) (typed_isGraph hg)
    intro x
    simp only [comp.app, pairMed, sndC.app, diagC_app]
    rw [tensorR_app, pairSeq_app_one, pairSeq_app_one]
    have := congrArg (fun w => funOf w x) (typed.arrowR_restrict hc hg)
    simpa [comp.app] using this.symm

end DomainTheory.DataTypesAsLattices

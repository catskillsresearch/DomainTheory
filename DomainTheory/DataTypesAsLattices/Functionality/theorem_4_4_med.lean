/-ai
Scott 1976, Theorem 4.4. If a, b, and c are retracts, f is a map from c to a, and g is a map from c to b, then the product mediator of f, g, and c is a map from c to a ⊗ b, its composite with the first projection is f, and its composite with the second projection is g.

The function-space equation is compared as graphs after unfolding the arrow and the mediator. Typing of f and of g, evaluated at c(x) and combined with the retract law for c, shows that a and b fix those applications. The diagonal and one product application compute one side, and the retract law for c, the diagonal, and two product applications compute the other, so the fixed-point equations identify them. Each projection equation is a graph comparison: the component laws, the diagonal, and the product application reduce it to the restriction of the typed arrow along c.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_zero
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_one
public import DomainTheory.DataTypesAsLattices.Functionality.tensorR_app
public import DomainTheory.DataTypesAsLattices.Functionality.diagC_app
public import DomainTheory.DataTypesAsLattices.Functionality.graph_funOf_ext
public import DomainTheory.DataTypesAsLattices.Functionality.typed_isGraph
public import DomainTheory.DataTypesAsLattices.Functionality.comp_isGraph

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Theorem 4.4.** Existence of the product mediator. -/
theorem theorem_4_4_med {a b c f g : Pomega}
    (_ha : Retract a) (_hb : Retract b) (hc : Retract c)
    (hf : typed f (arrowR c a)) (hg : typed g (arrowR c b)) :
    typed (pairMed f g c) (arrowR c (tensorR a b)) ∧
      comp fstC (pairMed f g c) = f ∧
      comp sndC (pairMed f g c) = g := by
  have hf' := typed_of_arrowR hf
  have hg' := typed_of_arrowR hg
  refine ⟨?_, ?_, ?_⟩
  · change pairMed f g c =
        funOf (arrowR c (tensorR a b)) (pairMed f g c)
    rw [arrowR_app, pairMed]
    apply graph_ext
    intro x
    have hfxc : funOf f (funOf c x) =
        funOf a (funOf f (funOf c x)) := by
      have := congrArg (fun w => funOf w (funOf c x)) hf'
      simpa [comp_app, retract_app hc] using this
    have hgxc : funOf g (funOf c x) =
        funOf b (funOf g (funOf c x)) := by
      have := congrArg (fun w => funOf w (funOf c x)) hg'
      simpa [comp_app, retract_app hc] using this
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
    simp only [comp_app]
    rw [hL, hR]
    exact congr (congrArg pairSeq hfxc) hgxc
  · apply graph_funOf_ext (comp_isGraph _ _) (typed_isGraph hf)
    intro x
    simp only [comp_app, pairMed, fstC_app, diagC_app]
    rw [tensorR_app, pairSeq_app_zero, pairSeq_app_zero]
    have := congrArg (fun w => funOf w x) (typed_arrowR_restrict hc hf)
    simpa [comp_app] using this.symm
  · apply graph_funOf_ext (comp_isGraph _ _) (typed_isGraph hg)
    intro x
    simp only [comp_app, pairMed, sndC_app, diagC_app]
    rw [tensorR_app, pairSeq_app_one, pairSeq_app_one]
    have := congrArg (fun w => funOf w x) (typed_arrowR_restrict hc hg)
    simpa [comp_app] using this.symm

end DomainTheory.DataTypesAsLattices

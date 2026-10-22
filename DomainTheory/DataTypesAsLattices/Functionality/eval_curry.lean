module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_zero
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_one
public import DomainTheory.DataTypesAsLattices.Functionality.tensorR_app
public import DomainTheory.DataTypesAsLattices.Functionality.evalC_app
public import DomainTheory.DataTypesAsLattices.Functionality.curryC_app3
public import DomainTheory.DataTypesAsLattices.Functionality.graph_funOf_ext
public import DomainTheory.DataTypesAsLattices.Functionality.typed_isGraph
public import DomainTheory.DataTypesAsLattices.Functionality.comp_isGraph

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, after (4.25).** `eval ∘ (curry(f) ⊗ b) = f`. -/
theorem eval_curry {a b c f : Pomega}
    (_ha : Retract a) (hb : Retract b) (_hc : Retract c)
    (hf : typed f (arrowR (tensorR a b) c)) :
    comp evalC (tensorR (funOf curryC f) b) = f := by
  have hf' := typed_of_arrowR hf
  apply graph_funOf_ext (comp_isGraph _ _) (typed_isGraph hf)
  intro u
  simp only [comp_app]
  rw [evalC_app, tensorR_app, pairSeq_app_zero, pairSeq_app_one, curryC_app3]
  have hfapp :
      funOf f (pairSeq (funOf u (ofNat 0)) (funOf b (funOf u (ofNat 1)))) =
        funOf c (funOf f (funOf (tensorR a b)
          (pairSeq (funOf u (ofNat 0)) (funOf b (funOf u (ofNat 1)))))) := by
    have := congrArg (fun w =>
      funOf w (pairSeq (funOf u (ofNat 0)) (funOf b (funOf u (ofNat 1))))) hf'
    simpa [comp_app] using this
  have hfu : funOf f u = funOf c (funOf f (funOf (tensorR a b) u)) := by
    have := congrArg (fun w => funOf w u) hf'
    simpa [comp_app] using this
  rw [hfapp, tensorR_app, pairSeq_app_zero, pairSeq_app_one, retract_app hb]
  rw [hfu, tensorR_app]

end DomainTheory.DataTypesAsLattices

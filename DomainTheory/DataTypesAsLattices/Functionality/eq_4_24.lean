module

public import DomainTheory.DataTypesAsLattices.Retracts.comp
public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.typed
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR
public import DomainTheory.DataTypesAsLattices.Retracts.tensorR
public import DomainTheory.DataTypesAsLattices.Retracts.evalC
public import DomainTheory.DataTypesAsLattices.Retracts.retract_app
public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_zero
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_one
public import DomainTheory.DataTypesAsLattices.Functionality.tensorR_app
public import DomainTheory.DataTypesAsLattices.Functionality.tensorR_isRetract
public import DomainTheory.DataTypesAsLattices.Functionality.evalC_app
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR_more

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem eq_4_24 {b c : Pomega} (hb : Retract b) (hc : Retract c) :
    typed (comp evalC (tensorR (arrowR b c) b))
      (arrowR (tensorR (arrowR b c) b) c) := by
  change comp evalC (tensorR (arrowR b c) b) =
    funOf (arrowR (tensorR (arrowR b c) b) c)
      (comp evalC (tensorR (arrowR b c) b))
  rw [arrowR.app]
  apply graph_ext
  intro u
  have hL :
      funOf evalC (funOf (tensorR (arrowR b c) b) u) =
        funOf c (funOf (funOf u (ofNat 0)) (funOf b (funOf u (ofNat 1)))) := by
    rw [evalC_app, tensorR_app, pairSeq_app_zero, pairSeq_app_one, arrowR.app]
    simp only [comp.app]
    rw [retract_app hb]
  have hR :
      funOf c (funOf evalC (funOf (tensorR (arrowR b c) b)
        (funOf (tensorR (arrowR b c) b) u))) =
        funOf c (funOf (funOf u (ofNat 0)) (funOf b (funOf u (ofNat 1)))) := by
    have hten := retract_app (tensorR_isRetract (arrowR.isRetract hb hc) hb) u
    rw [hten, hL, retract_app hc]
  simp only [comp.app]
  exact hL.trans hR.symm

end DomainTheory.DataTypesAsLattices

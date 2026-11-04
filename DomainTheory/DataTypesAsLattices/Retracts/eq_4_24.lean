module

public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.typed
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR
public import DomainTheory.DataTypesAsLattices.Retracts.tensorR
public import DomainTheory.DataTypesAsLattices.Retracts.evalC
public import DomainTheory.DataTypesAsLattices.Retracts.retract_app
public import DomainTheory.DataTypesAsLattices.Retracts.graphLemmas
public import DomainTheory.DataTypesAsLattices.Lambda.Language
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.eDense
public import DomainTheory.DataTypesAsLattices.Enumeration.PairSeq
public import DomainTheory.DataTypesAsLattices.Functionality.CombC
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
    rw [evalC_app, tensorR.app, PairSeq.app_zero, PairSeq.app_one, arrowR.app]
    simp only [comp.app]
    rw [retract_app hb]
  have hR :
      funOf c (funOf evalC (funOf (tensorR (arrowR b c) b)
        (funOf (tensorR (arrowR b c) b) u))) =
        funOf c (funOf (funOf u (ofNat 0)) (funOf b (funOf u (ofNat 1)))) := by
    have hten := retract_app (tensorR.isRetract (arrowR.isRetract hb hc) hb) u
    rw [hten, hL, retract_app hc]
  simp only [comp.app]
  exact hL.trans hR.symm

end DomainTheory.DataTypesAsLattices


module

public import DomainTheory.DataTypesAsLattices.Retracts.comp
public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.typed
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR
public import DomainTheory.DataTypesAsLattices.Retracts.fstC
public import DomainTheory.DataTypesAsLattices.Retracts.sndC
public import DomainTheory.DataTypesAsLattices.Retracts.tensorR
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.pairMed
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_zero
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_one
public import DomainTheory.DataTypesAsLattices.Functionality.tensorR_app
public import DomainTheory.DataTypesAsLattices.Functionality.diagC_app
public import DomainTheory.DataTypesAsLattices.Functionality.graph_funOf_ext
public import DomainTheory.DataTypesAsLattices.Functionality.typed_isGraph
public import DomainTheory.DataTypesAsLattices.Functionality.theorem_4_4_med
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR_more
public import DomainTheory.DataTypesAsLattices.Retracts.typed_more

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem theorem_4_4_med_unique {a b c f g h : Pomega}
    (ha : Retract a) (hb : Retract b) (hc : Retract c)
    (hf : typed f (arrowR c a)) (hg : typed g (arrowR c b))
    (hh : typed h (arrowR c (tensorR a b)))
    (hfst : comp fstC h = f) (hsnd : comp sndC h = g) :
    h = pairMed f g c := by
  apply graph_funOf_ext (typed_isGraph hh)
    (typed_isGraph (theorem_4_4_med ha hb hc hf hg).1)
  intro x
  have hh' := arrowR.typed_of hh
  have hx : funOf h x =
      funOf (tensorR a b) (funOf h (funOf c x)) := by
    have := congrArg (fun w => funOf w x) hh'
    simpa [comp.app] using this
  have h0 : funOf (funOf h x) (ofNat 0) = funOf f x := by
    have := congrArg (fun w => funOf w x) hfst
    simpa [comp.app, fstC.app] using this
  have h1 : funOf (funOf h x) (ofNat 1) = funOf g x := by
    have := congrArg (fun w => funOf w x) hsnd
    simpa [comp.app, sndC.app] using this
  rw [hx, tensorR_app]
  have hfx : funOf a (funOf (funOf h (funOf c x)) (ofNat 0)) = funOf f x := by
    have h0c : funOf (funOf h (funOf c x)) (ofNat 0) = funOf f (funOf c x) := by
      have := congrArg (fun w => funOf w (funOf c x)) hfst
      simpa [comp.app, fstC.app] using this
    rw [h0c]
    have := congrArg (fun w => funOf w x) (arrowR.typed_of hf)
    simpa [comp.app] using this.symm
  have hgx : funOf b (funOf (funOf h (funOf c x)) (ofNat 1)) = funOf g x := by
    have h1c : funOf (funOf h (funOf c x)) (ofNat 1) = funOf g (funOf c x) := by
      have := congrArg (fun w => funOf w (funOf c x)) hsnd
      simpa [comp.app, sndC.app] using this
    rw [h1c]
    have := congrArg (fun w => funOf w x) (arrowR.typed_of hg)
    simpa [comp.app] using this.symm
  rw [hfx, hgx]
  simp only [pairMed, comp.app, diagC_app, tensorR_app, pairSeq_app_zero,
    pairSeq_app_one]
  have hfr : funOf f (funOf c x) = funOf f x := by
    have := congrArg (fun w => funOf w x) (typed.arrowR_restrict hc hf)
    simpa [comp.app] using this.symm
  have hgr : funOf g (funOf c x) = funOf g x := by
    have := congrArg (fun w => funOf w x) (typed.arrowR_restrict hc hg)
    simpa [comp.app] using this.symm
  rw [hfr, hgr]

end DomainTheory.DataTypesAsLattices

module

public import DomainTheory.DataTypesAsLattices.Retracts.arrowR
public import DomainTheory.DataTypesAsLattices.Retracts.fstC
public import DomainTheory.DataTypesAsLattices.Retracts.sndC
public import DomainTheory.DataTypesAsLattices.Functionality.pairMed
import DomainTheory.DataTypesAsLattices.Graph.funOf_more
import DomainTheory.DataTypesAsLattices.Functionality.CombC
import DomainTheory.DataTypesAsLattices.Enumeration.PairSeq
import DomainTheory.DataTypesAsLattices.Retracts.typed_more
import DomainTheory.DataTypesAsLattices.Retracts.bot_isRetract
import DomainTheory.DataTypesAsLattices.Retracts.retract_app
import DomainTheory.DataTypesAsLattices.Retracts.graphLemmas

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

namespace theorem_4_4

theorem ii (x y : Pomega) :
    funOf (pairSeq x y) (ofNat 0) = x ∧
      funOf (pairSeq x y) (ofNat 1) = y :=
  ⟨seq2.zero x y, seq2.one x y⟩

theorem typed_iff {a b u : Pomega} :
    typed u (tensorR a b) ↔
      u = pairSeq (funOf u (ofNat 0)) (funOf u (ofNat 1)) ∧
        typed (funOf u (ofNat 0)) a ∧ typed (funOf u (ofNat 1)) b := by
  constructor
  · intro hu
    have hpair : u =
        pairSeq (funOf a (funOf u (ofNat 0)))
          (funOf b (funOf u (ofNat 1))) := by
      simpa [typed, tensorR.app] using hu
    have h0 : funOf u (ofNat 0) = funOf a (funOf u (ofNat 0)) := by
      have := congrArg (fun w => funOf w (ofNat 0)) hpair
      simpa [PairSeq.app_zero] using this
    have h1 : funOf u (ofNat 1) = funOf b (funOf u (ofNat 1)) := by
      have := congrArg (fun w => funOf w (ofNat 1)) hpair
      simpa [PairSeq.app_one] using this
    refine ⟨hpair.trans (congr (congrArg pairSeq h0.symm) h1.symm), h0, h1⟩
  · intro ⟨hpair, ha, hb⟩
    change u = funOf (tensorR a b) u
    rw [tensorR.app, ← ha, ← hb, ← hpair]

theorem med {a b c f g : Pomega}
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
      rw [diagC_app, tensorR.app, PairSeq.app_zero, PairSeq.app_one]
    have hR : funOf (tensorR a b)
        (funOf (tensorR f g) (funOf diagC (funOf c (funOf c x)))) =
        pairSeq (funOf a (funOf f (funOf c x)))
          (funOf b (funOf g (funOf c x))) := by
      rw [retract_app hc, diagC_app]
      have hinter :
          funOf (tensorR f g) (pairSeq (funOf c x) (funOf c x)) =
            pairSeq (funOf f (funOf c x)) (funOf g (funOf c x)) := by
        rw [tensorR.app, PairSeq.app_zero, PairSeq.app_one]
      rw [hinter, tensorR.app, PairSeq.app_zero, PairSeq.app_one]
    simp only [comp.app]
    rw [hL, hR]
    exact congr (congrArg pairSeq hfxc) hgxc
  · apply funOf.ext_graph (comp.isGraph _ _) (typed.isGraph hf)
    intro x
    simp only [comp.app, pairMed, fstC.app, diagC_app]
    rw [tensorR.app, PairSeq.app_zero, PairSeq.app_zero]
    have := congrArg (fun w => funOf w x) (typed.arrowR_restrict hc hf)
    simpa [comp.app] using this.symm
  · apply funOf.ext_graph (comp.isGraph _ _) (typed.isGraph hg)
    intro x
    simp only [comp.app, pairMed, sndC.app, diagC_app]
    rw [tensorR.app, PairSeq.app_one, PairSeq.app_one]
    have := congrArg (fun w => funOf w x) (typed.arrowR_restrict hc hg)
    simpa [comp.app] using this.symm

theorem med_unique {a b c f g h : Pomega}
    (ha : Retract a) (hb : Retract b) (hc : Retract c)
    (hf : typed f (arrowR c a)) (hg : typed g (arrowR c b))
    (hh : typed h (arrowR c (tensorR a b)))
    (hfst : comp fstC h = f) (hsnd : comp sndC h = g) :
    h = pairMed f g c := by
  apply funOf.ext_graph (typed.isGraph hh)
    (typed.isGraph (med ha hb hc hf hg).1)
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
  rw [hx, tensorR.app]
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
  simp only [pairMed, comp.app, diagC_app, tensorR.app, PairSeq.app_zero,
    PairSeq.app_one]
  have hfr : funOf f (funOf c x) = funOf f x := by
    have := congrArg (fun w => funOf w x) (typed.arrowR_restrict hc hf)
    simpa [comp.app] using this.symm
  have hgr : funOf g (funOf c x) = funOf g x := by
    have := congrArg (fun w => funOf w x) (typed.arrowR_restrict hc hg)
    simpa [comp.app] using this.symm
  rw [hfr, hgr]

end theorem_4_4

theorem theorem_4_4 :
    (∀ x y, funOf (pairSeq x y) (ofNat 0) = x ∧
      funOf (pairSeq x y) (ofNat 1) = y) ∧
      Retract botElem :=
  ⟨fun x y => theorem_4_4.ii x y, bot_isRetract⟩

end DomainTheory.DataTypesAsLattices

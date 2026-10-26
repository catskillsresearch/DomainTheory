module

public import DomainTheory.DataTypesAsLattices.Retracts.arrowR
public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.retractLe
public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext
public import DomainTheory.DataTypesAsLattices.Retracts.comp_app
public import DomainTheory.DataTypesAsLattices.Retracts.theorem_4_3_more
public import DomainTheory.DataTypesAsLattices.Retracts.eq_4_11_comp

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

namespace arrowR

theorem isRetract {a b : Pomega} (ha : Retract a) (hb : Retract b) :
    Retract (arrowR a b) := by
  constructor
  change arrowR a b =
    graph (fun x => funOf (arrowR a b) (funOf (arrowR a b) x))
  apply graph_ext
  intro u
  rw [theorem_4_3.i ha hb, app]

theorem mono {a b a' b' : Pomega}
    (hab : _root_.DomainTheory.DataTypesAsLattices.retractLe a a')
    (hbb : _root_.DomainTheory.DataTypesAsLattices.retractLe b b') :
    _root_.DomainTheory.DataTypesAsLattices.retractLe (arrowR a b) (arrowR a' b') := by
  constructor
  · have h : arrowR (comp a' a) (comp b b') = arrowR a b := by
      rw [← hab.2, ← hbb.1]
    exact (h.symm.trans (eq_4_11_comp a b a' b').symm)
  · have h : arrowR (comp a a') (comp b' b) = arrowR a b := by
      rw [← hab.1, ← hbb.2]
    exact (h.symm.trans (eq_4_11_comp a' b' a b).symm)

theorem functor {a b a' b' f f' : Pomega}
    (hf : typed f (arrowR a b)) (hf' : typed f' (arrowR a' b')) :
    typed (arrowR f f') (arrowR (arrowR b a') (arrowR a b')) := by
  change arrowR f f' =
    funOf (arrowR (arrowR b a') (arrowR a b')) (arrowR f f')
  rw [app]
  have inner := eq_4_11_comp f f' b a'
  have outer := eq_4_11_comp a b' (comp b f) (comp f' a')
  have hf1 := typed_of hf
  have hf2 := typed_of hf'
  apply Eq.symm
  calc
    comp (arrowR a b') (comp (arrowR f f') (arrowR b a'))
        = comp (arrowR a b') (arrowR (comp b f) (comp f' a')) := by rw [inner]
    _ = arrowR (comp (comp b f) a) (comp b' (comp f' a')) := outer
    _ = arrowR f f' := by
      apply graph_ext
      intro u
      apply graph_ext
      intro x
      have hfx : funOf f x = funOf b (funOf f (funOf a x)) := by
        simpa [comp_app] using congrArg (fun w => funOf w x) hf1
      have hf'y : ∀ y, funOf f' y = funOf b' (funOf f' (funOf a' y)) := by
        intro y
        simpa [comp_app] using congrArg (fun w => funOf w y) hf2
      simp only [comp_app]
      rw [hfx]
      exact (hf'y _).symm

end arrowR

end DomainTheory.DataTypesAsLattices

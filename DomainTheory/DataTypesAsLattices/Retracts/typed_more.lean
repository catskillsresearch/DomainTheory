module

public import DomainTheory.DataTypesAsLattices.Retracts.typed
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR
public import DomainTheory.DataTypesAsLattices.Retracts.comp
public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.theorem_4_3_more
public import DomainTheory.DataTypesAsLattices.Retracts.retract_app
public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext
public import DomainTheory.DataTypesAsLattices.Graph.graph

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

namespace typed

theorem arrowR_range {a b u : Pomega}
    (hb : Retract b) (hu : typed u (arrowR a b)) :
    u = comp b u := by
  have hu' := arrowR.typed_of hu
  rw [hu']
  apply graph_ext
  intro x
  simp only [comp.app]
  rw [retract_app hb]

theorem arrowR_restrict {a b u : Pomega}
    (ha : Retract a) (hu : typed u (arrowR a b)) :
    u = comp u a := by
  have hu' := arrowR.typed_of hu
  have h : comp (comp b (comp u a)) a = comp b (comp u a) := by
    apply graph_ext
    intro x
    simp only [comp.app]
    rw [retract_app ha]
  have : comp u a = comp (comp b (comp u a)) a := by
    conv_lhs => rw [hu']
  exact ((this.trans h).trans hu'.symm).symm

theorem arrowR_iff {a b u : Pomega} (ha : Retract a) (_hb : Retract b) :
    typed u (arrowR a b) ↔
      u = comp u a ∧ ∀ x, typed x a → typed (funOf u x) b := by
  constructor
  · intro hu
    exact ⟨typed.arrowR_restrict ha hu, fun x hx => theorem_4_3.ii hu hx⟩
  · intro ⟨hrest, hval⟩
    change u = funOf (arrowR a b) u
    rw [arrowR.app]
    apply Eq.trans hrest
    apply graph_ext
    intro x
    have hx : typed (funOf a x) a := (retract_app ha x).symm
    have hbx : funOf u (funOf a x) = funOf b (funOf u (funOf a x)) :=
      hval (funOf a x) hx
    simp only [comp.app]
    exact hbx

theorem comp {a b c f f' : Pomega}
    (ha : Retract a) (hb : Retract b) (_hc : Retract c)
    (hf : typed f (arrowR a b)) (hf' : typed f' (arrowR b c)) :
    typed (DomainTheory.DataTypesAsLattices.comp f' f) (arrowR a c) := by
  have hf1 := arrowR.typed_of hf
  have hf2 := arrowR.typed_of hf'
  change DomainTheory.DataTypesAsLattices.comp f' f =
      funOf (arrowR a c) (DomainTheory.DataTypesAsLattices.comp f' f)
  rw [arrowR.app]
  apply graph_ext
  intro x
  have hfx : funOf f x = funOf b (funOf f (funOf a x)) := by
    simpa [DomainTheory.DataTypesAsLattices.comp.app] using
      congrArg (fun w => funOf w x) hf1
  have hrest := typed.arrowR_restrict ha hf
  have hfa : funOf f (funOf a x) = funOf f x := by
    simpa [DomainTheory.DataTypesAsLattices.comp.app] using
      (congrArg (fun w => funOf w x) hrest).symm
  have hf'fx : funOf f' (funOf f x) =
      funOf c (funOf f' (funOf b (funOf f x))) := by
    simpa [DomainTheory.DataTypesAsLattices.comp.app] using
      congrArg (fun w => funOf w (funOf f x)) hf2
  have hrange := typed.arrowR_range hb hf
  have hbval : funOf b (funOf f (funOf a x)) = funOf f (funOf a x) := by
    simpa [DomainTheory.DataTypesAsLattices.comp.app] using
      (congrArg (fun w => funOf w (funOf a x)) hrange).symm
  simp only [DomainTheory.DataTypesAsLattices.comp.app]
  rw [hf'fx, ← hfa, hbval, hfa]

end typed

end DomainTheory.DataTypesAsLattices

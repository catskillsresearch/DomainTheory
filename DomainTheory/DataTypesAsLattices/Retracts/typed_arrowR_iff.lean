module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic
public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR_app
public import DomainTheory.DataTypesAsLattices.Retracts.theorem_4_3_ii
public import DomainTheory.DataTypesAsLattices.Retracts.typed_arrowR_restrict

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem typed_arrowR_iff {a b u : Pomega} (ha : Retract a) (_hb : Retract b) :
    typed u (arrowR a b) ↔
      u = comp u a ∧ ∀ x, typed x a → typed (funOf u x) b := by
  constructor
  · intro hu
    exact ⟨typed_arrowR_restrict ha hu, fun x hx => theorem_4_3_ii hu hx⟩
  · intro ⟨hrest, hval⟩
    change u = funOf (arrowR a b) u
    rw [arrowR_app]
    apply Eq.trans hrest
    apply graph_ext
    intro x
    have hx : typed (funOf a x) a := (retract_app ha x).symm
    have hbx : funOf u (funOf a x) = funOf b (funOf u (funOf a x)) :=
      hval (funOf a x) hx
    simp only [comp_app]
    exact hbx

end DomainTheory.DataTypesAsLattices

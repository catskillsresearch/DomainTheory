/-ai
A set is typed by the function space of a retract a with a retract b exactly when the set equals its composite with a and sends every a-typed set to a b-typed set. The retract hypothesis on b is not used.

Typing gives the restriction equation and, for each a-typed argument, the value condition of Theorem 4.3 (ii). Conversely, rewrite the desired typing equation by the function-space application law and the restriction equation, and compare graphs. At each argument, the application of a is typed by a because a retract is idempotent, so the value hypothesis identifies the two sides after composition.
ai-/
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









































theorem typed_arrowR_iff {a b u : Pomega} (ha : IsRetract a) (_hb : IsRetract b) :
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

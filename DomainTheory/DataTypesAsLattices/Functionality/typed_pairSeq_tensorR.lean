/-ai
The pair of x and y is typed by the tensor retract of a and b if and only if x is typed by a and y is typed by b.

From a tensor typing, the tensor equation and the two projection laws for pair sequences rewrite the pair as the pair of the two retracted components, and injectivity of pair sequences splits the typings. Conversely, those same rewrites, read against the two typing equations, give the tensor typing.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_zero
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_one
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_inj
public import DomainTheory.DataTypesAsLattices.Functionality.tensorR_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem typed_pairSeq_tensorR (a b x y : Pomega) :
    typed (pairSeq x y) (tensorR a b) ↔ typed x a ∧ typed y b := by
  constructor
  · intro h
    have h' : pairSeq x y =
        pairSeq (funOf a x) (funOf b y) := by
      rw [typed, tensorR_app, pairSeq_app_zero, pairSeq_app_one] at h
      exact h
    exact pairSeq_inj h'
  · intro ⟨hx, hy⟩
    rw [typed, tensorR_app, pairSeq_app_zero, pairSeq_app_one, ← hx, ← hy]

end DomainTheory.DataTypesAsLattices

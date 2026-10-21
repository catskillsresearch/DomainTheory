/-ai
Sequence pairing is injective in both arguments.

Evaluating both sides of an equality of pairs at zero, and rewriting by the zero-place equation, gives equality of the left arguments. Evaluating at one, and rewriting by the one-place equation, gives equality of the right arguments.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_zero
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_one

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem pairSeq_inj {x y x' y' : Pomega} (h : pairSeq x y = pairSeq x' y') :
    x = x' ∧ y = y' := by
  constructor
  · have := congrArg (fun w => funOf w (ofNat 0)) h
    rw [pairSeq_app_zero, pairSeq_app_zero] at this
    exact this
  · have := congrArg (fun w => funOf w (ofNat 1)) h
    rw [pairSeq_app_one, pairSeq_app_one] at this
    exact this

end DomainTheory.DataTypesAsLattices


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

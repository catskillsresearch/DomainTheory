module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices














































/-- **Scott 1976, Theorem 4.4 (ii), pairing form.** A pair-as-function
projects to its components. -/
theorem theorem_4_4_ii (x y : Pomega) :
    funOf (pairSeq x y) (ofNat 0) = x ∧
      funOf (pairSeq x y) (ofNat 1) = y :=
  ⟨seq2_app_zero x y, seq2_app_one x y⟩

end DomainTheory.DataTypesAsLattices

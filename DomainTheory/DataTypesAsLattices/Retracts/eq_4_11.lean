/-ai
Applying the function space from a to b to the application of the function space from a' to b' at u equals b composed after b' composed after u composed after a', and then after a. This is Scott's computation (4.11).

Both applications are rewritten by the application law for function-space retracts.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (4.11).** Action of composed function-space retracts. -/
theorem eq_4_11 (a b a' b' u : Pomega) :
    funOf (arrowR a b) (funOf (arrowR a' b') u) =
      comp b (comp (comp b' (comp u a')) a) := by
  rw [arrowR_app, arrowR_app]

end DomainTheory.DataTypesAsLattices

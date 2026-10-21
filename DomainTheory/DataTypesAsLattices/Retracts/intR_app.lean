/-ai
Applying the integer retract to u returns the doubly strict conditional of u on the numeral zero and the conditional of the application of the integer retract to the predecessor of u on u and u.

The identification of the integer retract with the integer functional is applied at u. Reversing that equality and rewriting by the application law for the functional yields the conditional formula.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic
public import DomainTheory.DataTypesAsLattices.Retracts.intF_app
public import DomainTheory.DataTypesAsLattices.Retracts.intR_eq_intF

@[expose] public section


namespace DomainTheory.DataTypesAsLattices














































theorem intR_app (u : Pomega) :
    funOf intR u =
      dcondSet u (ofNat 0) (dcondSet (funOf intR (predSet u)) u u) := by
  have h := congrArg (fun a => funOf a u) intR_eq_intF
  simpa [intF_app] using h.symm

end DomainTheory.DataTypesAsLattices

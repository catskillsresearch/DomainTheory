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

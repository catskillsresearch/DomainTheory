
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem normalized_finite_app (p : ℕ) (u : Pomega) :
    funOf (graph (fun y => funOf (e p) y)) u = funOf (e p) u :=
  beta (funOf_isScottContinuous (e p)) u

end DomainTheory.DataTypesAsLattices

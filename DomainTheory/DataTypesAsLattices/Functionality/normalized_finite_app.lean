/-ai
Application of the graph of application of the finite set e p equals application of e p itself.

This is β-conversion, since application of e p is Scott continuous.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices






























theorem normalized_finite_app (p : ℕ) (u : Pomega) :
    funOf (graph (fun y => funOf (e p) y)) u = funOf (e p) u :=
  beta (funOf_isScottContinuous (e p)) u

end DomainTheory.DataTypesAsLattices

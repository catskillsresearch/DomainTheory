
module

public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem normalized_finite_app (p : ℕ) (u : Pomega) :
    funOf (graph (fun y => funOf (e p) y)) u = funOf (e p) u :=
  beta (funOf.isScottContinuous (e p)) u

end DomainTheory.DataTypesAsLattices

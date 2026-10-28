module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.condSet
public import DomainTheory.DataTypesAsLattices.Lambda.condC
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Lambda.condC_more
@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

theorem condC_app2 (x y : Pomega) :
    funOf (funOf condC x) y = graph (fun z => condSet z x y) :=
  condC.beta2 x y

end DomainTheory.DataTypesAsLattices

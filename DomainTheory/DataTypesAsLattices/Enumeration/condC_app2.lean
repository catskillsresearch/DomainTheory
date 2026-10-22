/-ai
Applying the conditional combinator to x and then to y yields the graph of the map sending z to the conditional set of z with branches x and y.

This is the two-argument beta law for the conditional combinator.
ai-/
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


theorem condC_app2 (x y : Pomega) :
    funOf (funOf condC x) y = graph (fun z => condSet z x y) :=
  condC_beta2 x y

end DomainTheory.DataTypesAsLattices

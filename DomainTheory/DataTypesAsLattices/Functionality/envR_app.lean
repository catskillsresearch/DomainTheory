/-ai
Application of the environment retract at t is the graph of n mapped to the application of the lambda retract to the application of t at n.

This is the beta rule for the Scott continuity of that environment map, evaluated at t.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.envR_map_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

































theorem envR_app (t : Pomega) :
    funOf envR t = graph (fun n => funOf lambR (funOf t n)) :=
  beta envR_map_isScottContinuous t

end DomainTheory.DataTypesAsLattices

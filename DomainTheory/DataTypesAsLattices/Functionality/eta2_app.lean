/-ai
Application, at x, of the graph of z mapped to the graph of y mapped to the double application of f at z and then y, equals the graph of y mapped to the double application of f at x and then y.

This is the beta rule for the Scott continuity of that eta map, evaluated at x.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.eta2_map_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem eta2_app (f x : Pomega) :
    funOf (graph (fun z => graph (fun y => funOf (funOf f z) y))) x =
      graph (fun y => funOf (funOf f x) y) :=
  beta (eta2_map_isScottContinuous f) x

end DomainTheory.DataTypesAsLattices

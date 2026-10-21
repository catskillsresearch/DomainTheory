/-ai
Application of S at f is the graph of the map sending v to the graph of the map sending x to the application of f at x applied to v at x.

This is beta reduction, using Scott continuity of the outer map of S.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.Scomb_map_cont

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem Scomb_beta (f : Pomega) :
    funOf Scomb f =
      graph (fun v => graph (fun x => funOf (funOf f x) (funOf v x))) :=
  beta Scomb_map_cont f

end DomainTheory.DataTypesAsLattices

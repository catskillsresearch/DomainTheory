/-ai
Applying the S combinator to a function yields the graph of the map sending a second function to the graph of the pointwise application of the first function to the second.

This is beta reduction for continuity of the outer S map.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.Scomb_map_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem Scomb_app (f : Pomega) :
    funOf Scomb f =
      graph (fun v => graph (fun x => funOf (funOf f x) (funOf v x))) :=
  beta Scomb_map_isScottContinuous f

end DomainTheory.DataTypesAsLattices

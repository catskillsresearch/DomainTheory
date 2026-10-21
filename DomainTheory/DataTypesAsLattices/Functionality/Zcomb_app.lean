/-ai
Applying the combinator Z at a stage to a function yields the graph of the iterator of that function at that stage.

This is beta reduction for continuity of the combinator map.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.Zcomb_map_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem Zcomb_app (n : ℕ) (f : Pomega) :
    funOf (Zcomb n) f = graph (fun x => Z n f x) :=
  beta (Zcomb_map_isScottContinuous n) f

end DomainTheory.DataTypesAsLattices

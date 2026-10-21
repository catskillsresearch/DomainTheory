/-ai
Applying the function-space retract from a to b to u returns the composition of b after u after a.

This is β-conversion, from Scott continuity of that composition map.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR_map_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem arrowR_app (a b u : Pomega) :
    funOf (arrowR a b) u = comp b (comp u a) :=
  beta (arrowR_map_isScottContinuous a b) u

end DomainTheory.DataTypesAsLattices

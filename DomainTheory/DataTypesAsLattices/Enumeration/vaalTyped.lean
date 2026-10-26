module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR
public import DomainTheory.DataTypesAsLattices.Retracts.Icomb
public import DomainTheory.DataTypesAsLattices.Retracts.treeR
public import DomainTheory.DataTypesAsLattices.Enumeration.vaalC
public import DomainTheory.DataTypesAsLattices.Retracts.typed
public import DomainTheory.DataTypesAsLattices.Functionality.typed_apply_retract
public import DomainTheory.DataTypesAsLattices.Functionality.treeR_isRetract
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR_more

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

/-- **Scott 1976, (4.46).** `vaal : tree → id` as a typed map. -/
def vaalTyped : Pomega := funOf (arrowR treeR Icomb) vaalC


theorem vaalTyped_typed :
    typed vaalTyped (arrowR treeR Icomb) := by
  simpa [vaalTyped] using
    typed_apply_retract (arrowR.isRetract treeR_isRetract Icomb.isRetract)

end DomainTheory.DataTypesAsLattices

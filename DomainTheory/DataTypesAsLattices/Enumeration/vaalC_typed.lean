module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code





























































theorem vaalC_typed :
    typed vaalTyped (arrowR treeR Icomb) :=
  typed_apply_retract (arrowR_isRetract treeR_isRetract Icomb_isRetract)

end DomainTheory.DataTypesAsLattices

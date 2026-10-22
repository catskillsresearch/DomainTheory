module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem unpairWRec_succ (k n : ℕ) :
    unpairWRec k (n + 1) =
      if k < triangle (n + 1) then unpairWRec k n else n + 1 :=
  rfl

end DomainTheory.DataTypesAsLattices

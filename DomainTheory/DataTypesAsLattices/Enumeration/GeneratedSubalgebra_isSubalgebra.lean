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


theorem GeneratedSubalgebra_isSubalgebra (xs : List Pomega) :
    Subalgebra (GeneratedSubalgebra xs) := by
  constructor
  constructor
  · intro A hA _
    exact hA.out.1
  · intro u v hu hv A hA hxs
    exact hA.out.2 (hu A hA hxs) (hv A hA hxs)

end DomainTheory.DataTypesAsLattices

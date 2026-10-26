module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Enumeration.Subalgebra

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

/-- The least combinatory subalgebra containing every member of `xs`. -/
def GeneratedSubalgebra (xs : List Pomega) : Set Pomega :=
  {u | ∀ A : Set Pomega, Subalgebra A →
    (∀ x, x ∈ xs → x ∈ A) → u ∈ A}

namespace GeneratedSubalgebra

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem generator {xs : List Pomega} {x : Pomega}
    (hx : x ∈ xs) : x ∈ GeneratedSubalgebra xs :=
  fun _ _ hxs => hxs x hx

theorem isSubalgebra (xs : List Pomega) :
    Subalgebra (GeneratedSubalgebra xs) := by
  constructor
  constructor
  · intro A hA _
    exact hA.out.1
  · intro u v hu hv A hA hxs
    exact hA.out.2 (hu A hA hxs) (hv A hA hxs)

end GeneratedSubalgebra

end DomainTheory.DataTypesAsLattices

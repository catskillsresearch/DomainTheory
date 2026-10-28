module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Enumeration.Gcomb

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

class Subalgebra (A : Set Pomega) : Prop where
  out : Gcomb ∈ A ∧ ∀ ⦃u v⦄, u ∈ A → v ∈ A → funOf u v ∈ A

end DomainTheory.DataTypesAsLattices

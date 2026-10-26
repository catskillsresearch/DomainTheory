module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.BasicInst85

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

/-- Combinatory subalgebra: contains `G` and is closed under application. -/
class Subalgebra (A : Set Pomega) : Prop where
  out : Gcomb ∈ A ∧ ∀ ⦃u v⦄, u ∈ A → v ∈ A → funOf u v ∈ A

end DomainTheory.DataTypesAsLattices

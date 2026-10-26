module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.seq2
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

/-- The paper's single generator of a finite tuple: `cond(⟨xs⟩)(G)`. -/
def packList : List Pomega → Pomega
  | [] => botElem
  | x :: xs => seq2 x (packList xs)

end DomainTheory.DataTypesAsLattices

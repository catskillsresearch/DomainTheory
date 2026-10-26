module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Pomega.pair

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def pack4 (n0 n1 n2 m : ℕ) : ℕ :=
  Nat.pair n0 (Nat.pair n1 (Nat.pair n2 m))

namespace pack4

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

def proj1 (t : ℕ) : ℕ := (Nat.unpair t).1

def proj2 (t : ℕ) : ℕ := (Nat.unpair (Nat.unpair t).2).1

def proj3 (t : ℕ) : ℕ := (Nat.unpair (Nat.unpair (Nat.unpair t).2).2).1

def proj4 (t : ℕ) : ℕ := (Nat.unpair (Nat.unpair (Nat.unpair t).2).2).2

end pack4

end DomainTheory.DataTypesAsLattices

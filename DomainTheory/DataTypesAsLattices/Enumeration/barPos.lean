module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

/-- **Scott 1976, (3.15).** Positive branch of `ū`: `⟨1, u, x₁⟩`. -/
def barPos (u x : Pomega) : Pomega :=
  seqCons (ofNat 1) (seq2 u (funOf x (ofNat 1)))

end DomainTheory.DataTypesAsLattices

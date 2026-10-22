/-ai
The environment filterEnv sends index 3 to the filter realizer, 4 to the pairing combinator, 5 to the dollar combinator, 6 to the predecessor combinator, and 7 to the top element, and sends every other index to the bottom element.
ai-/
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.BasicInst85
public import DomainTheory.DataTypesAsLattices.Enumeration.filterRealizer

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def filterEnv : ℕ → Pomega
  | 3 => filterRealizer
  | 4 => pairComb
  | 5 => dollarC
  | 6 => predC
  | 7 => topElem
  | _ => botElem

end DomainTheory.DataTypesAsLattices

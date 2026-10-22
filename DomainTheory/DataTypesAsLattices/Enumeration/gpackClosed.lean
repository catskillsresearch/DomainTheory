/-ai
The term gpackClosed is the nested binary sequencing of the closed successor term, the closed predecessor term, the closed conditional term, the closed K term, and the closed S term.
ai-/
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.BasicInst85
public import DomainTheory.DataTypesAsLattices.Enumeration.seq2Term
public import DomainTheory.DataTypesAsLattices.Enumeration.sucClosed
public import DomainTheory.DataTypesAsLattices.Enumeration.predClosed
public import DomainTheory.DataTypesAsLattices.Enumeration.condClosed
public import DomainTheory.DataTypesAsLattices.Enumeration.kClosed
public import DomainTheory.DataTypesAsLattices.Enumeration.sClosed

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def gpackClosed : Term :=
  seq2Term sucClosed
    (seq2Term predClosed
      (seq2Term condClosed (seq2Term kClosed sClosed)))

end DomainTheory.DataTypesAsLattices

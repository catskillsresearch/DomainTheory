/-ai
The positive-branch term conses the successor of zero onto the sequencing of variable 1 with the application of variable 2 to the successor of zero. It is the term for the positive branch of Scott's bar operator, the triple of 1, u, and the first tail of x.
ai-/
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.BasicInst85
public import DomainTheory.DataTypesAsLattices.Enumeration.seq2Term
public import DomainTheory.DataTypesAsLattices.Enumeration.seqConsTerm

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

/-- Term for the positive branch `⟨1,u,x₁⟩` of Scott's bar operator. -/
def barPosTerm : Term :=
  seqConsTerm (.succ .zero)
    (seq2Term (.var 1) (.app (.var 2) (.succ .zero)))

end DomainTheory.DataTypesAsLattices

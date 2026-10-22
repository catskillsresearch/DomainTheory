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

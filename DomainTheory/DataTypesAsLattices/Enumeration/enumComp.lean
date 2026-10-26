module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

/-- Composition in the semigroup `FUN`. -/
def enumComp (u v : Pomega) : Pomega :=
  graph (fun x => funOf u (funOf v x))

end DomainTheory.DataTypesAsLattices

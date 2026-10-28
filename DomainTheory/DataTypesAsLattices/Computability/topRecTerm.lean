module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Graph.lam
public import DomainTheory.DataTypesAsLattices.Computability.pack4
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Lambda.envSet
public import DomainTheory.DataTypesAsLattices.Lambda.topRec
public import DomainTheory.DataTypesAsLattices.Lambda.interp
public import DomainTheory.DataTypesAsLattices.Enumeration.Avoids
public import DomainTheory.DataTypesAsLattices.Lambda.eq_2_15

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def topRecTerm : Term :=
  .lam 0 (.cond (.lam 1 .zero) .zero (.succ (.var 0)))

namespace topRecTerm

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem interp :
    interp topRecTerm (fun _ => botElem) = graph topRec := by
  apply congrArg graph
  funext v
  simp[topRec, _root_.DomainTheory.DataTypesAsLattices.interp, envSet, Function.update, _root_.DomainTheory.DataTypesAsLattices.eq_2_15]

end topRecTerm

end DomainTheory.DataTypesAsLattices

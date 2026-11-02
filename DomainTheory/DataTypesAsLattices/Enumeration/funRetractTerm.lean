module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.Language
public import DomainTheory.DataTypesAsLattices.Graph.lam
public import DomainTheory.DataTypesAsLattices.Pomega.eDense
public import DomainTheory.DataTypesAsLattices.Lambda.interp
public import DomainTheory.DataTypesAsLattices.Retracts.funRetract
public import DomainTheory.DataTypesAsLattices.Enumeration.Avoids

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def funRetractTerm : Term :=
  .lam 0 (.lam 1 (.app (.var 0) (.var 1)))

namespace funRetractTerm

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem interp :
    interp funRetractTerm (fun _ => botElem) = funRetract := by
  unfold funRetractTerm funRetract
  simp[_root_.DomainTheory.DataTypesAsLattices.interp, envSet, Function.update]

end funRetractTerm

end DomainTheory.DataTypesAsLattices

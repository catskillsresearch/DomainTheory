module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Graph.lam
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Lambda.envSet
public import DomainTheory.DataTypesAsLattices.Lambda.interp
public import DomainTheory.DataTypesAsLattices.Lambda.condC
public import DomainTheory.DataTypesAsLattices.Enumeration.Avoids

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def condClosed : Term :=
  .lam 4 (.lam 5 (.lam 6 (.cond (.var 6) (.var 4) (.var 5))))

namespace condClosed

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem avoids8 : condClosed.Avoids 8 := by
  simp[condClosed, Term.Avoids]

theorem interp (ρ : ℕ → Pomega) : interp condClosed ρ = condC := by
  simp[condClosed, condC, envSet, Function.update, _root_.DomainTheory.DataTypesAsLattices.interp]

end condClosed

end DomainTheory.DataTypesAsLattices

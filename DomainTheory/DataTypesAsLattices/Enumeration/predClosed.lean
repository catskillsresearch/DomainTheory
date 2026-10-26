module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Graph.lam
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Lambda.envSet
public import DomainTheory.DataTypesAsLattices.Lambda.predC
public import DomainTheory.DataTypesAsLattices.Lambda.interp
public import DomainTheory.DataTypesAsLattices.Enumeration.Avoids

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def predClosed : Term := .lam 4 (.pred (.var 4))

namespace predClosed

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem avoids8 : predClosed.Avoids 8 := by
  simp[predClosed, Term.Avoids]

theorem interp (ρ : ℕ → Pomega) : interp predClosed ρ = predC := by
  simp[predClosed, predC, envSet, Function.update, _root_.DomainTheory.DataTypesAsLattices.interp]

end predClosed

end DomainTheory.DataTypesAsLattices

module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.Language
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Pomega.eDense
public import DomainTheory.DataTypesAsLattices.Lambda.interp
public import DomainTheory.DataTypesAsLattices.Enumeration.Avoids

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def kClosed : Term := .lam 4 (.lam 5 (.var 4))

namespace kClosed

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem avoids8 : kClosed.Avoids 8 := by
  simp[kClosed, Term.Avoids]

theorem interp (ρ : ℕ → Pomega) : interp kClosed ρ = Kcomb := by
  simp[kClosed, Kcomb, envSet, Function.update, _root_.DomainTheory.DataTypesAsLattices.interp]

end kClosed

end DomainTheory.DataTypesAsLattices

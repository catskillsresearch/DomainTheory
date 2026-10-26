module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Graph.lam
public import DomainTheory.DataTypesAsLattices.Enumeration.gpackClosed
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Lambda.envSet
public import DomainTheory.DataTypesAsLattices.Lambda.zeroC
public import DomainTheory.DataTypesAsLattices.Lambda.interp
public import DomainTheory.DataTypesAsLattices.Enumeration.Avoids
public import DomainTheory.DataTypesAsLattices.Enumeration.Gcomb

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def gClosed : Term := .lam 3 (.cond (.var 3) gpackClosed .zero)

namespace gClosed

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem interp (ρ : ℕ → Pomega) : interp gClosed ρ = Gcomb := by
  unfold gClosed Gcomb
  apply congrArg graph
  funext z
  simp only [_root_.DomainTheory.DataTypesAsLattices.interp]
  rw [gpackClosed.interp]
  simp [envSet, Function.update, zeroC]

end gClosed

end DomainTheory.DataTypesAsLattices

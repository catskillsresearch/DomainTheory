
module

public import DomainTheory.DataTypesAsLattices.Lambda.interp
public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Graph.lam
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Enumeration.Avoids
public import DomainTheory.DataTypesAsLattices.Lambda.Scomb
public import DomainTheory.DataTypesAsLattices.Lambda.envSet

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def sClosed : Term :=
  .lam 4 (.lam 5 (.lam 6
    (.app (.app (.var 4) (.var 6)) (.app (.var 5) (.var 6)))))

namespace sClosed

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem avoids8 : sClosed.Avoids 8 := by
  simp[sClosed, Term.Avoids]

theorem interp (ρ : ℕ → Pomega) : interp sClosed ρ = Scomb := by
  simp[sClosed, Scomb, envSet, Function.update, _root_.DomainTheory.DataTypesAsLattices.interp]

end sClosed

end DomainTheory.DataTypesAsLattices

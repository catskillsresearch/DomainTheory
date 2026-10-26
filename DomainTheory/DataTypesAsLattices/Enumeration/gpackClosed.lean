module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Enumeration.seq2Term
public import DomainTheory.DataTypesAsLattices.Enumeration.sucClosed
public import DomainTheory.DataTypesAsLattices.Enumeration.predClosed
public import DomainTheory.DataTypesAsLattices.Enumeration.condClosed
public import DomainTheory.DataTypesAsLattices.Enumeration.kClosed
public import DomainTheory.DataTypesAsLattices.Enumeration.sClosed
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Lambda.interp
public import DomainTheory.DataTypesAsLattices.Enumeration.Avoids
public import DomainTheory.DataTypesAsLattices.Enumeration.Gpack

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def gpackClosed : Term :=
  seq2Term sucClosed
    (seq2Term predClosed
      (seq2Term condClosed (seq2Term kClosed sClosed)))

namespace gpackClosed

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem interp (ρ : ℕ → Pomega) :
    interp gpackClosed ρ = Gpack := by
  unfold gpackClosed Gpack
  rw [seq2Term.interp _ _ ρ sucClosed.avoids8 (seq2Term.avoids8 _ _),
    seq2Term.interp _ _ ρ predClosed.avoids8 (seq2Term.avoids8 _ _),
    seq2Term.interp _ _ ρ condClosed.avoids8 (seq2Term.avoids8 _ _),
    seq2Term.interp _ _ ρ kClosed.avoids8 sClosed.avoids8,
    sucClosed.interp, predClosed.interp, condClosed.interp,
    kClosed.interp, sClosed.interp]

end gpackClosed

end DomainTheory.DataTypesAsLattices

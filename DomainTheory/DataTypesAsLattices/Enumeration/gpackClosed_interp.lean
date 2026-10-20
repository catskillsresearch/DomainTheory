module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.seq2Term_interp
public import DomainTheory.DataTypesAsLattices.Enumeration.sucClosed_avoids8
public import DomainTheory.DataTypesAsLattices.Enumeration.predClosed_avoids8
public import DomainTheory.DataTypesAsLattices.Enumeration.condClosed_avoids8
public import DomainTheory.DataTypesAsLattices.Enumeration.kClosed_avoids8
public import DomainTheory.DataTypesAsLattices.Enumeration.sClosed_avoids8
public import DomainTheory.DataTypesAsLattices.Enumeration.seq2Term_avoids8
public import DomainTheory.DataTypesAsLattices.Enumeration.sucClosed_interp
public import DomainTheory.DataTypesAsLattices.Enumeration.predClosed_interp
public import DomainTheory.DataTypesAsLattices.Enumeration.condClosed_interp
public import DomainTheory.DataTypesAsLattices.Enumeration.kClosed_interp
public import DomainTheory.DataTypesAsLattices.Enumeration.sClosed_interp

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


























































theorem gpackClosed_interp (ρ : ℕ → Pomega) :
    interp gpackClosed ρ = Gpack := by
  unfold gpackClosed Gpack
  rw [seq2Term_interp _ _ ρ sucClosed_avoids8 (seq2Term_avoids8 _ _),
    seq2Term_interp _ _ ρ predClosed_avoids8 (seq2Term_avoids8 _ _),
    seq2Term_interp _ _ ρ condClosed_avoids8 (seq2Term_avoids8 _ _),
    seq2Term_interp _ _ ρ kClosed_avoids8 sClosed_avoids8,
    sucClosed_interp, predClosed_interp, condClosed_interp,
    kClosed_interp, sClosed_interp]

end DomainTheory.DataTypesAsLattices

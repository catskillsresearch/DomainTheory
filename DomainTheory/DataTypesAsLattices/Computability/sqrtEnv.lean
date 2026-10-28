module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Computability.mulC
public import DomainTheory.DataTypesAsLattices.Computability.leC
public import DomainTheory.DataTypesAsLattices.Computability.pack4
public import DomainTheory.DataTypesAsLattices.Computability.botElem_combinatory

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def sqrtEnv : ℕ → Pomega
  | 3 => leC
  | 4 => mulC
  | _ => botElem

namespace sqrtEnv

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem combinatory : ∀ i, IsCombinatory (sqrtEnv i)
  | 3 => leC.combinatory
  | 4 => mulC.combinatory
  | 0 | 1 | 2 => botElem_combinatory
  | _ + 5 => botElem_combinatory

end sqrtEnv

end DomainTheory.DataTypesAsLattices

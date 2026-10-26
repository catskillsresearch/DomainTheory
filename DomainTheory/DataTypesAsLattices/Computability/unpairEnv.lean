module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Computability.subC
public import DomainTheory.DataTypesAsLattices.Computability.mulC
public import DomainTheory.DataTypesAsLattices.Computability.leC
public import DomainTheory.DataTypesAsLattices.Computability.sqrtC
public import DomainTheory.DataTypesAsLattices.Computability.pack4

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def unpairEnv : ℕ → Pomega
  | 1 => sqrtC
  | 2 => subC
  | 3 => mulC
  | 4 => leC
  | _ => botElem

namespace unpairEnv

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem combinatory : ∀ i, IsCombinatory (unpairEnv i)
  | 1 => sqrtC.combinatory
  | 2 => subC.combinatory
  | 3 => mulC.combinatory
  | 4 => leC.combinatory
  | 0 => botElem_combinatory
  | _ + 5 => botElem_combinatory

end unpairEnv

end DomainTheory.DataTypesAsLattices

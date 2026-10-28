module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Computability.addC
public import DomainTheory.DataTypesAsLattices.Computability.subC
public import DomainTheory.DataTypesAsLattices.Computability.mulC
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Computability.pack4
public import DomainTheory.DataTypesAsLattices.Lambda.zeroC
public import DomainTheory.DataTypesAsLattices.Lambda.predC
public import DomainTheory.DataTypesAsLattices.Lambda.predC_more
public import DomainTheory.DataTypesAsLattices.Lambda.eq_2_6

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def arithEnv : ℕ → Pomega
  | 0 => addC
  | 1 => mulC
  | 2 => subC
  | _ => botElem

namespace arithEnv

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem combinatory : ∀ i, IsCombinatory (arithEnv i)
  | 0 => addC.combinatory
  | 1 => mulC.combinatory
  | 2 => subC.combinatory
  | n + 3 => by
    have hbot : funOf predC zeroC = botElem := by
      rw [predC.app]; exact _root_.DomainTheory.DataTypesAsLattices.eq_2_6
    simpa [arithEnv, hbot] using
      IsCombinatory.app IsCombinatory.pred IsCombinatory.zero

end arithEnv

end DomainTheory.DataTypesAsLattices

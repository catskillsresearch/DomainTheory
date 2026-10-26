module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.condC
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Computability.pack4
public import DomainTheory.DataTypesAsLattices.Lambda.eq_2_7_succ
public import DomainTheory.DataTypesAsLattices.Lambda.eq_2_7_zero
public import DomainTheory.DataTypesAsLattices.Lambda.condC_more
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat_more
@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

/-- `cond 1 0 n` is `1` on `0` and `0` on positive numerals. -/
def isZeroC : Pomega := funOf (funOf condC (ofNat 1)) (ofNat 0)

namespace isZeroC

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem combinatory : IsCombinatory isZeroC :=
  .app (.app .cond (ofNat.combinatory 1)) (ofNat.combinatory 0)


theorem succ (n : ℕ) : funOf isZeroC (ofNat (n + 1)) = ofNat 0 := by
  simp only [isZeroC]
  rw [condC.beta3]
  exact eq_2_7_succ (ofNat 1) (ofNat 0) n


theorem zero : funOf isZeroC (ofNat 0) = ofNat 1 := by
  simp only [isZeroC]
  rw [condC.beta3, eq_2_7_zero]

end isZeroC

end DomainTheory.DataTypesAsLattices

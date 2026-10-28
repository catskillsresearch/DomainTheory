module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda.Kcomb
public import DomainTheory.DataTypesAsLattices.Lambda.Scomb
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Computability.subC
public import DomainTheory.DataTypesAsLattices.Computability.isZeroC

public import DomainTheory.DataTypesAsLattices.Graph.Basic.notation3
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Computability.pack4
public import DomainTheory.DataTypesAsLattices.Lambda.Kcomb_more
public import DomainTheory.DataTypesAsLattices.Lambda.Scomb_more
@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def leC : Pomega :=
  Scomb ⬝ (Kcomb ⬝ (Scomb ⬝ (Kcomb ⬝ isZeroC))) ⬝ subC

namespace leC

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem combinatory : IsCombinatory leC :=
  .app (.app .S (.app .K (.app .S (.app .K isZeroC.combinatory))))
    subC.combinatory

theorem realizes2 (n m : ℕ) :
    funOf (funOf leC (ofNat n)) (ofNat m) =
      ofNat (if n ≤ m then 1 else 0) := by
  unfold leC
  rw [Scomb.beta3, Kcomb.beta2, Scomb.beta3, Kcomb.beta2, subC.realizes2]
  by_cases h : n ≤ m
  · have : n - m = 0 := Nat.sub_eq_zero_of_le h
    simp [h, this, isZeroC.zero]
  · have : 0 < n - m := Nat.sub_pos_of_lt (Nat.not_le.mp h)
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero this.ne'
    simp [h, hk, isZeroC.succ]

end leC

end DomainTheory.DataTypesAsLattices

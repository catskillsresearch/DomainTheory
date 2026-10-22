module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.subC_realizes2
public import DomainTheory.DataTypesAsLattices.Computability.isZeroC_zero
public import DomainTheory.DataTypesAsLattices.Computability.isZeroC_succ

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4


theorem leC_realizes2 (n m : ℕ) :
    funOf (funOf leC (ofNat n)) (ofNat m) =
      ofNat (if n ≤ m then 1 else 0) := by
  unfold leC
  rw [Scomb_beta3, Kcomb_beta2, Scomb_beta3, Kcomb_beta2, subC_realizes2]
  by_cases h : n ≤ m
  · have : n - m = 0 := Nat.sub_eq_zero_of_le h
    simp [h, this, isZeroC_zero]
  · have : 0 < n - m := Nat.sub_pos_of_lt (Nat.not_le.mp h)
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero this.ne'
    simp [h, hk, isZeroC_succ]

end DomainTheory.DataTypesAsLattices

module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.addC_realizes2
public import DomainTheory.DataTypesAsLattices.Computability.subC_realizes2
public import DomainTheory.DataTypesAsLattices.Computability.mulC_realizes2

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4


theorem pairComb_app (n m : ℕ) :
    funOf (funOf pairComb (ofNat n)) (ofNat m) = ofNat (Nat.pair n m) := by
  unfold pairComb pairTerm
  rw [theorem_2_2_beta, theorem_2_2_beta]
  simp [interp, envSet, Function.update, arithEnv]
  rw [subC_realizes2, mulC_realizes2, mulC_realizes2, addC_realizes2,
    addC_realizes2, addC_realizes2]
  simp [Nat.pair]
  by_cases h : n < m
  · have : m - n ≠ 0 := Nat.sub_ne_zero_of_lt h
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero this
    rw [hk, eq_2_7_succ]
    simp [h]
  · have : m - n = 0 := Nat.sub_eq_zero_of_le (Nat.not_lt.mp h)
    rw [this, eq_2_7_zero]
    simp [h]

end DomainTheory.DataTypesAsLattices

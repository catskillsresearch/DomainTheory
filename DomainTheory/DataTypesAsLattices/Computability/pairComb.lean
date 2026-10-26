module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda.interp
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Computability.pairTerm
public import DomainTheory.DataTypesAsLattices.Computability.arithEnv
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Computability.addC
public import DomainTheory.DataTypesAsLattices.Computability.subC
public import DomainTheory.DataTypesAsLattices.Computability.pack4
public import DomainTheory.DataTypesAsLattices.Computability.mulC
public import DomainTheory.DataTypesAsLattices.Lambda.envSet
public import DomainTheory.DataTypesAsLattices.Lambda.ofComb

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def pairComb : Pomega := interp pairTerm arithEnv

namespace pairComb

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem app (n m : ℕ) :
    funOf (funOf pairComb (ofNat n)) (ofNat m) = ofNat (Nat.pair n m) := by
  unfold pairComb pairTerm
  rw [theorem_2_2.beta, theorem_2_2.beta]
  simp [interp, envSet, Function.update, arithEnv]
  rw [subC.realizes2, mulC.realizes2, mulC.realizes2, addC.realizes2,
    addC.realizes2, addC.realizes2]
  simp [Nat.pair]
  by_cases h : n < m
  · have : m - n ≠ 0 := Nat.sub_ne_zero_of_lt h
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero this
    rw [hk, eq_2_7_succ]
    simp [h]
  · have : m - n = 0 := Nat.sub_eq_zero_of_le (Nat.not_lt.mp h)
    rw [this, eq_2_7_zero]
    simp [h]

theorem combinatory : IsCombinatory pairComb := by
  rw [pairComb, theorem_2_4.complete]
  exact ofComb.combinatory _ _ arithEnv.combinatory

end pairComb

end DomainTheory.DataTypesAsLattices

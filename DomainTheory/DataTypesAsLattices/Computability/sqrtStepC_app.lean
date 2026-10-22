module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.mulC_realizes2
public import DomainTheory.DataTypesAsLattices.Computability.leC_realizes2

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4


theorem sqrtStepC_app (n i a : ℕ) :
    ((sqrtStepC ⬝ ofNat n) ⬝ ofNat i) ⬝ ofNat a =
      ofNat (if (a + 1) * (a + 1) ≤ n then a + 1 else a) := by
  unfold sqrtStepC sqrtStepTerm
  rw [theorem_2_2_beta, theorem_2_2_beta, theorem_2_2_beta]
  simp only [interp, envSet, Function.update_self,
    Function.update_of_ne (by decide : (3 : ℕ) ≠ 0),
    Function.update_of_ne (by decide : (4 : ℕ) ≠ 0),
    Function.update_of_ne (by decide : (3 : ℕ) ≠ 1),
    Function.update_of_ne (by decide : (4 : ℕ) ≠ 1),
    Function.update_of_ne (by decide : (3 : ℕ) ≠ 2),
    Function.update_of_ne (by decide : (4 : ℕ) ≠ 2), sqrtEnv]
  simp [Function.update]
  rw [succSet_ofNat, mulC_realizes2, leC_realizes2]
  by_cases h : (a + 1) * (a + 1) ≤ n
  · simp [h, eq_2_7_succ]
  · simp [h, eq_2_7_zero]

end DomainTheory.DataTypesAsLattices

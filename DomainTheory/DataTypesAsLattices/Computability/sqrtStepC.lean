module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda.interp
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Computability.sqrtEnv
public import DomainTheory.DataTypesAsLattices.Computability.sqrtStepTerm
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Graph.Basic.notation3
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Computability.pack4
public import DomainTheory.DataTypesAsLattices.Computability.mulC
public import DomainTheory.DataTypesAsLattices.Computability.leC
public import DomainTheory.DataTypesAsLattices.Lambda.envSet
public import DomainTheory.DataTypesAsLattices.Lambda.ofComb
public import DomainTheory.DataTypesAsLattices.Lambda.succSet
public import DomainTheory.DataTypesAsLattices.Lambda.succSet_more

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def sqrtStepC : Pomega := interp sqrtStepTerm sqrtEnv

namespace sqrtStepC

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem app (n i a : ℕ) :
    ((sqrtStepC ⬝ ofNat n) ⬝ ofNat i) ⬝ ofNat a =
      ofNat (if (a + 1) * (a + 1) ≤ n then a + 1 else a) := by
  unfold sqrtStepC sqrtStepTerm
  rw [theorem_2_2.beta, theorem_2_2.beta, theorem_2_2.beta]
  simp only [interp, envSet, Function.update_self,
    Function.update_of_ne (by decide : (3 : ℕ) ≠ 0),
    Function.update_of_ne (by decide : (4 : ℕ) ≠ 0),
    Function.update_of_ne (by decide : (3 : ℕ) ≠ 1),
    Function.update_of_ne (by decide : (4 : ℕ) ≠ 1),
    Function.update_of_ne (by decide : (3 : ℕ) ≠ 2),
    Function.update_of_ne (by decide : (4 : ℕ) ≠ 2), sqrtEnv]
  simp [Function.update]
  rw [succSet.ofNat, mulC.realizes2, leC.realizes2]
  by_cases h : (a + 1) * (a + 1) ≤ n
  · simp [h, eq_2_7_succ]
  · simp [h, eq_2_7_zero]

theorem combinatory : IsCombinatory sqrtStepC := by
  rw [sqrtStepC, theorem_2_4.complete]
  exact ofComb.combinatory _ _ sqrtEnv.combinatory

end sqrtStepC

end DomainTheory.DataTypesAsLattices

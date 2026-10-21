/-ai
The combinator unpairFstC realizes the first component of Nat.unpair.

Unfold the combinator and its term and apply the beta law theorem_2_2_beta. Simplifying the interpretation places the square-root, subtraction, multiplication, and comparison combinators of unpairEnv at the free indices. The realization lemmas for those combinators, together with succSet_ofNat, reduce the body. Unfold Nat.unpair and split on whether n minus the square of its integer square root lies strictly below that square root. In the positive case the successor of the difference is at most the square root, and eq_2_7_succ closes the goal. In the other case that bound fails, and eq_2_7_zero closes the goal.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.subC_realizes2
public import DomainTheory.DataTypesAsLattices.Computability.mulC_realizes2
public import DomainTheory.DataTypesAsLattices.Computability.leC_realizes2
public import DomainTheory.DataTypesAsLattices.Computability.sqrtC_realizes

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code



attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4






























theorem unpairFstC_realizes : Realizes unpairFstC (fun n => n.unpair.1) := fun n => by
  rw [unpairFstC, unpairFstTerm, theorem_2_2_beta]
  simp only [unpairTestTerm, unpairDeltaTerm, unpairSquareTerm, unpairSqrtTerm,
    interp, envSet, Function.update_self,
    Function.update_of_ne (by decide : (1 : ℕ) ≠ 0),
    Function.update_of_ne (by decide : (2 : ℕ) ≠ 0),
    Function.update_of_ne (by decide : (3 : ℕ) ≠ 0),
    Function.update_of_ne (by decide : (4 : ℕ) ≠ 0), unpairEnv]
  rw [sqrtC_realizes, mulC_realizes2, subC_realizes2, succSet_ofNat,
    leC_realizes2]
  unfold Nat.unpair
  by_cases h : n - Nat.sqrt n * Nat.sqrt n < Nat.sqrt n
  · have hle : n - Nat.sqrt n * Nat.sqrt n + 1 ≤ Nat.sqrt n :=
      Nat.succ_le_iff.mpr h
    simp [h, hle, eq_2_7_succ]
  · have hle : ¬n - Nat.sqrt n * Nat.sqrt n + 1 ≤ Nat.sqrt n := by omega
    simp [h, hle, eq_2_7_zero]

end DomainTheory.DataTypesAsLattices

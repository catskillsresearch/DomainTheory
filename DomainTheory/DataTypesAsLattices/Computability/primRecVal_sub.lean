/-ai
Primitive recursion from the numeral k with step subStepC, run for n steps, equals the numeral of the truncated difference k − n.

The case n = 0 is the definition of primRecVal. For a successor, the recursive clause unfolds the value, and the definition of subStepC together with Kcomb_beta2 replaces the step by safePredC. The inductive hypothesis replaces the previous value by the numeral k − n. If that difference is zero, then k − (n + 1) is zero and safePredC_zero gives the numeral 0. If it is a successor k′, then k − (n + 1) equals k′ and safePredC_succ gives that numeral.
ai-/
module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.safePredC_zero
public import DomainTheory.DataTypesAsLattices.Computability.safePredC_succ

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4


theorem primRecVal_sub (k : ℕ) : ∀ n,
    primRecVal (ofNat k) subStepC n = ofNat (k - n)
  | 0 => by simp [primRecVal]
  | n + 1 => by
    calc primRecVal (ofNat k) subStepC (n + 1)
        = funOf (funOf subStepC (ofNat n))
            (primRecVal (ofNat k) subStepC n) := rfl
      _ = funOf safePredC (primRecVal (ofNat k) subStepC n) := by
          simp [subStepC, Kcomb_beta2]
      _ = funOf safePredC (ofNat (k - n)) := by rw [primRecVal_sub k n]
      _ = ofNat (k - (n + 1)) := by
          cases h : k - n with
          | zero =>
            have : k - (n + 1) = 0 := by omega
            simp [safePredC_zero, this]
          | succ k' =>
            have : k - (n + 1) = k' := by omega
            simp [safePredC_succ, this]

end DomainTheory.DataTypesAsLattices

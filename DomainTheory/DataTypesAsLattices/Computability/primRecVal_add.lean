/-ai
Primitive recursion from the numeral k with step addStepC, run for n steps, equals the numeral k + n.

The case n = 0 is reflexivity. For a successor, the recursive clause writes the value as the application of addStepC at the numeral n to the value at n. The definition of addStepC and the K-combinator law Kcomb_beta2 replace that step by sucC. The inductive hypothesis replaces the previous value by the numeral k + n, and sucC_app together with succSet_ofNat yields the numeral k + n + 1.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4


theorem primRecVal_add (k : ℕ) : ∀ n,
    primRecVal (ofNat k) addStepC n = ofNat (k + n)
  | 0 => rfl
  | n + 1 => by
    calc primRecVal (ofNat k) addStepC (n + 1)
        = funOf (funOf addStepC (ofNat n))
            (primRecVal (ofNat k) addStepC n) := rfl
      _ = funOf sucC (primRecVal (ofNat k) addStepC n) := by
          simp [addStepC, Kcomb_beta2]
      _ = funOf sucC (ofNat (k + n)) := by rw [primRecVal_add k n]
      _ = ofNat (k + n + 1) := by rw [sucC_app, succSet_ofNat]

end DomainTheory.DataTypesAsLattices

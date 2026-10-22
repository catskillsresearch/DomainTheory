/-ai
Primitive recursion from the numeral 0, whose step is the K combinator applied to addition of the numeral k, run for n steps, equals the numeral k · n.

The case n = 0 is the definition of primRecVal. For a successor, the recursive clause unfolds the value, and Kcomb_beta2 together with the inductive hypothesis replaces it by addition of the numeral k to the numeral k · n. The realization addC_realizes2 gives the numeral k + k · n, and the successor law for multiplication together with commutativity of addition gives the numeral k · (n + 1).
ai-/
module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.addC_realizes2

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4


theorem primRecVal_mul (k : ℕ) : ∀ n,
    primRecVal (ofNat 0) (funOf Kcomb (funOf addC (ofNat k))) n = ofNat (k * n)
  | 0 => by simp [primRecVal]
  | n + 1 => by
    calc primRecVal (ofNat 0) (funOf Kcomb (funOf addC (ofNat k))) (n + 1)
        = funOf (funOf (funOf Kcomb (funOf addC (ofNat k))) (ofNat n))
            (primRecVal (ofNat 0) (funOf Kcomb (funOf addC (ofNat k))) n) :=
          rfl
      _ = funOf (funOf addC (ofNat k))
            (ofNat (k * n)) := by
          rw [Kcomb_beta2, primRecVal_mul k n]
      _ = ofNat (k + k * n) := addC_realizes2 k (k * n)
      _ = ofNat (k * (n + 1)) := by rw [Nat.mul_succ, Nat.add_comm]

end DomainTheory.DataTypesAsLattices

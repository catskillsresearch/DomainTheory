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

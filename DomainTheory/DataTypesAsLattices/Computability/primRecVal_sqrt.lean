module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda.primRecVal
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Computability.pack4
public import DomainTheory.DataTypesAsLattices.Computability.sqrtIter
public import DomainTheory.DataTypesAsLattices.Computability.sqrtStepC
public import DomainTheory.DataTypesAsLattices.Graph.Basic.notation3
@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code




theorem primRecVal_sqrt (n : ℕ) : ∀ k,
    primRecVal (ofNat 0) (sqrtStepC ⬝ ofNat n) k = ofNat (sqrtIter n k)
  | 0 => rfl
  | k + 1 => by
      rw [show primRecVal (ofNat 0) (sqrtStepC ⬝ ofNat n) (k + 1) =
        ((sqrtStepC ⬝ ofNat n) ⬝ ofNat k) ⬝
          primRecVal (ofNat 0) (sqrtStepC ⬝ ofNat n) k by rfl,
        primRecVal_sqrt n k, sqrtStepC.app]
      rfl

end DomainTheory.DataTypesAsLattices

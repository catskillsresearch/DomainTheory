module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.valNat_unionCode
public import DomainTheory.DataTypesAsLattices.Enumeration.valNat_fin
public import DomainTheory.DataTypesAsLattices.Enumeration.valNat_condCode
public import DomainTheory.DataTypesAsLattices.Enumeration.unionOperator_app

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code













theorem valNat_myhillCase2Code (j n m : ℕ) :
    valNat (myhillCase2Code j n m) =
      e j ∪ condSet (valNat m) (valNat n) (valNat n) := by
  simp only [myhillCase2Code, valNat_apply, valNat_unionCode, valNat_fin,
    valNat_condCode, condC_beta3]
  exact unionOperator_app _ _

end DomainTheory.DataTypesAsLattices

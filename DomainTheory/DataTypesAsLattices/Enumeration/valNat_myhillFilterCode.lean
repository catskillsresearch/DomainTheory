/-ai
The numerical evaluator sends the Myhill filter code of m to the set of j such that no stage at most j enumerates m.

Unfold the code, apply the application law for the evaluator, replace the filter-operator code by the filter combinator, and rewrite by equation (3.12) and the application law for the filter combinator.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.eq_3_12
public import DomainTheory.DataTypesAsLattices.Enumeration.filterC_app
public import DomainTheory.DataTypesAsLattices.Enumeration.valNat_filterOp

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem valNat_myhillFilterCode (m : ℕ) :
    valNat (myhillFilterCode m) = {j | ∀ i ≤ j, haltEnum i ≠ m} := by
  rw [myhillFilterCode, valNat_apply, valNat_filterOp, eq_3_12, filterC_app]

end DomainTheory.DataTypesAsLattices

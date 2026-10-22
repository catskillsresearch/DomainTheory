/-ai
If the finite set coded by j is contained in the numerical value of n, and the numerical value of m is distinct from bottom, then the numerical evaluator sends the second Myhill case code of j, n, and m to its value at n.

Rewrite by the second-case evaluation. The conditional with equal branches and a test distinct from bottom equals the common branch, and the union of a set with a subset on the left equals the larger set.
ai-/
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.condSet_same
public import DomainTheory.DataTypesAsLattices.Enumeration.valNat_myhillCase2Code

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem valNat_myhillCase2Code_ne_bot (j n m : ℕ)
    (hj : e j ⊆ valNat n) (hm : valNat m ≠ botElem) :
    valNat (myhillCase2Code j n m) = valNat n := by
  rw [valNat_myhillCase2Code, condSet_same _ _ hm]
  exact Set.union_eq_self_of_subset_left hj

end DomainTheory.DataTypesAsLattices

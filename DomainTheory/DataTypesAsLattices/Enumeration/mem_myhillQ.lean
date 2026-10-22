/-ai
A number k belongs to the Myhill set of a valuation at a function f if and only if the second component of the computational unpairing of k belongs to the value of f at the finite code of the first component.

From membership, k is the pair of some j and m with m in that value, and the computational unpairing of the pair is the pair (j, m). Conversely, k equals the pair of the two components of its computational unpairing, so those components witness membership.
ai-/
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.unpairComp_eq

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem mem_myhillQ (f : ℕ → ℕ) (k : ℕ) :
    k ∈ myhillQ valNat f ↔
      (unpairComp k).2 ∈ valNat (f (fin (unpairComp k).1)) := by
  constructor
  · intro ⟨j, m, hk, hm⟩
    have : unpairComp k = (j, m) := by
      rw [unpairComp_eq, hk, unpair_pair]
    simpa [this] using hm
  · intro hm
    refine ⟨(unpairComp k).1, (unpairComp k).2, ?_, hm⟩
    rw [unpairComp_eq, pair_unpair]

end DomainTheory.DataTypesAsLattices

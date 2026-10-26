module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Enumeration.valNat
public import DomainTheory.DataTypesAsLattices.Enumeration.fin
public import DomainTheory.DataTypesAsLattices.Enumeration.myhillQ
public import DomainTheory.DataTypesAsLattices.Enumeration.unpairComp
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
      rw [unpairComp.eq, hk, unpair_pair]
    simpa [this] using hm
  · intro hm
    refine ⟨(unpairComp k).1, (unpairComp k).2, ?_, hm⟩
    rw [unpairComp.eq, pair_unpair]

end DomainTheory.DataTypesAsLattices

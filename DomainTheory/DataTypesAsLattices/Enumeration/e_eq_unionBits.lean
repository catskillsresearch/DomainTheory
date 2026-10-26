module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Enumeration.unionBits
public import DomainTheory.DataTypesAsLattices.Enumeration.bitList
@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


theorem e_eq_unionBits (j : ℕ) : e j = unionBits (bitList j) := by
  ext n
  constructor
  · intro hn
    have hnle : n ≤ j := mem_e_le hn
    have hbit : j.testBit n := by simpa [e] using hn
    have : n ∈ bitList j := by
      simp [bitList, List.mem_filter, List.mem_range, Nat.lt_succ_of_le hnle, hbit]
    simpa [unionBits.eq] using this
  · intro hn
    have : n ∈ bitList j := by simpa [unionBits.eq] using hn
    simp [bitList, List.mem_filter] at this
    simpa [e] using this.2

end DomainTheory.DataTypesAsLattices

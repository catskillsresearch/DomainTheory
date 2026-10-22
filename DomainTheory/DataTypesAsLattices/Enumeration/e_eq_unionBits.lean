module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.unionBits_eq

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
    simpa [unionBits_eq] using this
  · intro hn
    have : n ∈ bitList j := by simpa [unionBits_eq] using hn
    simp [bitList, List.mem_filter] at this
    simpa [e] using this.2

end DomainTheory.DataTypesAsLattices

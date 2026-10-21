/-ai
The enumeration element of j equals the union of the bits in the bit list of j.

Compare membership of an index n. If n belongs to the enumeration of j, then n is at most j and the n-th bit of j is set, so n lies in the bit list and therefore in the union of those bits. Conversely, membership in the union means membership in the bit list, and simplifying the filter membership shows that the corresponding bit is set, so n belongs to the enumeration of j.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
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

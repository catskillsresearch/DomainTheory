/-ai
The conditional of the numeral 0 between G and bottom equals G. This is Scott's Theorem 3.2 (i): the zero test selects G.

Comparing elements, the first clause of the conditional is membership in G. The second clause simplifies to a contradiction at the numeral 0. Every member of G satisfies the first clause.
ai-/

module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Theorem 3.2 (i).** The zero test selects `G`. -/
theorem theorem_3_2_i : condSet (ofNat 0) Gcomb botElem = Gcomb := by
  ext n
  constructor
  · intro hn
    rcases hn with ⟨hG, _⟩ | ⟨_, ⟨k, hk⟩⟩
    · exact hG
    · simp [ofNat] at hk
  · intro hG
    exact Or.inl ⟨hG, rfl⟩

end DomainTheory.DataTypesAsLattices

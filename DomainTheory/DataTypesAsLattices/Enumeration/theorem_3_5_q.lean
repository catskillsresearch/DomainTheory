/-ai
In the Myhill–Shepherdson construction of Theorem 3.5, the pair of j and m belongs to the Myhill operator of val and p if and only if m belongs to val of p at the fin-code of j.

Membership in the operator supplies indices whose pair equals the given pair and whose second index lies in the corresponding value; injectivity of pairing forces the indices to be j and m. Conversely, the pair itself, together with the membership, is a witness.
ai-/

module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


































































/-- **Scott 1976, Theorem 3.5 (Myhill–Shepherdson), construction.** -/
theorem theorem_3_5_q (val : ℕ → Pomega) (p : ℕ → ℕ) (j m : ℕ) :
    pair j m ∈ myhillQ val p ↔ m ∈ val (p (fin j)) := by
  constructor
  · intro ⟨j', m', hp, hm⟩
    obtain ⟨rfl, rfl⟩ := pair_inj hp
    exact hm
  · intro hm
    exact ⟨j, m, rfl, hm⟩

end DomainTheory.DataTypesAsLattices

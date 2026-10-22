
module

public import Mathlib.Computability.Halting
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

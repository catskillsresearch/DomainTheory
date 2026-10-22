module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.e_subset_ofNat_iff

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem mem_funOf_ofNat (u : Pomega) (n m : ℕ) :
    m ∈ funOf u (ofNat n) ↔ pair 0 m ∈ u ∨ pair (2 ^ n) m ∈ u := by
  constructor
  · intro ⟨code, hsub, hp⟩
    rcases (e_subset_ofNat_iff code n).mp hsub with rfl | rfl
    · exact Or.inl hp
    · exact Or.inr hp
  · intro h
    rcases h with hp | hp
    · exact ⟨0, by simp [e_zero], hp⟩
    · exact ⟨2 ^ n, by simp [e_pow2, ofNat], hp⟩

end DomainTheory.DataTypesAsLattices

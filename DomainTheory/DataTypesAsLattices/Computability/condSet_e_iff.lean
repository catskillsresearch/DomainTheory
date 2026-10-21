/-ai
A number m lies in the conditional of the finite sets coded by n₂, n₀, and n₁ if and only if either bit m of n₀ and bit 0 of n₂ are set, or bit m of n₁ is set and 2 ≤ n₂.

In one direction, membership lies in the zero branch or the positive branch. The bit characterization of finite sets translates the zero branch, and the same characterization together with the criterion for a bit past position 0 translates the positive branch. The converse repacks those bit conditions into the two branches of the conditional.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.pos_bit_iff

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem condSet_e_iff (n0 n1 n2 m : ℕ) :
    m ∈ condSet (e n2) (e n0) (e n1) ↔
      (n0.testBit m = true ∧ n2.testBit 0 = true) ∨
        (n1.testBit m = true ∧ 2 ≤ n2) := by
  constructor
  · intro h
    rcases h with ⟨hm, h0⟩ | ⟨hm, ⟨k, hk⟩⟩
    · exact Or.inl ⟨mem_e.mp hm, mem_e.mp h0⟩
    · exact Or.inr ⟨mem_e.mp hm, (pos_bit_iff n2).1 ⟨k, mem_e.mp hk⟩⟩
  · intro h
    rcases h with ⟨hm, h0⟩ | ⟨hm, hn2⟩
    · exact Or.inl ⟨mem_e.mpr hm, mem_e.mpr h0⟩
    · obtain ⟨k, hk⟩ := (pos_bit_iff n2).2 hn2
      exact Or.inr ⟨mem_e.mpr hm, k, mem_e.mpr hk⟩

end DomainTheory.DataTypesAsLattices

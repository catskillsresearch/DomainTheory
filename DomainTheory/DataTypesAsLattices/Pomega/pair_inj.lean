/-ai
Pairing is injective: if the pair of n₁ and m₁ equals the pair of n₂ and m₂, then n₁ equals n₂ and m₁ equals m₂.

The triangular bounds place each pair at least at the triangular number of its component sum and strictly below the triangular number of that sum plus one. The two sums are equal, because a strict inequality either way would push one pair strictly below itself by monotonicity of the triangular numbers. Equality of the pairs and of the sums then cancels the common triangular number, so the second components agree, and cancellation in the sums gives the first components.
ai-/
module

public import Mathlib.Data.Nat.Bitwise
import all Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Lattice.Bounded
import all Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
import all Mathlib.Data.Set.Lattice.Disjoint
public import DomainTheory.DataTypesAsLattices.Pomega.Basic
public import DomainTheory.DataTypesAsLattices.Pomega.triangle_le_of_le
public import DomainTheory.DataTypesAsLattices.Pomega.triangle_le_pair

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem pair_inj {n₁ m₁ n₂ m₂ : ℕ} (h : pair n₁ m₁ = pair n₂ m₂) :
    n₁ = n₂ ∧ m₁ = m₂ := by
  have h1 := triangle_le_pair n₁ m₁
  have h2 := triangle_le_pair n₂ m₂
  have hw : n₁ + m₁ = n₂ + m₂ := by
    rcases lt_trichotomy (n₁ + m₁) (n₂ + m₂) with hlt | heq | hgt
    · have hle : triangle (n₁ + m₁ + 1) ≤ triangle (n₂ + m₂) :=
        triangle_le_of_le (Nat.succ_le_of_lt hlt)
      have : pair n₁ m₁ < pair n₁ m₁ :=
        calc
          pair n₁ m₁ < triangle (n₁ + m₁ + 1) := h1.2
          _ ≤ triangle (n₂ + m₂) := hle
          _ ≤ pair n₂ m₂ := h2.1
          _ = pair n₁ m₁ := h.symm
      exact (lt_irrefl _ this).elim
    · exact heq
    · have hle : triangle (n₂ + m₂ + 1) ≤ triangle (n₁ + m₁) :=
        triangle_le_of_le (Nat.succ_le_of_lt hgt)
      have : pair n₂ m₂ < pair n₂ m₂ :=
        calc
          pair n₂ m₂ < triangle (n₂ + m₂ + 1) := h2.2
          _ ≤ triangle (n₁ + m₁) := hle
          _ ≤ pair n₁ m₁ := h1.1
          _ = pair n₂ m₂ := h
      exact (lt_irrefl _ this).elim
  have hm : m₁ = m₂ := by
    have : triangle (n₁ + m₁) + m₁ = triangle (n₂ + m₂) + m₂ := h
    rw [hw] at this
    exact Nat.add_left_cancel this
  have hn : n₁ = n₂ := Nat.add_right_cancel (hw.trans (by rw [hm]))
  exact ⟨hn, hm⟩

end DomainTheory.DataTypesAsLattices

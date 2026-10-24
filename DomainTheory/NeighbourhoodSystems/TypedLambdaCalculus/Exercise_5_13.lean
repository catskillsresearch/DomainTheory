module

public import Aesop.BuiltinRules
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Nat.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.ToDual
public import Mathlib.Tactic.ToAdditive

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise513
section
/-- One step of the diagonal walk: the cell holding `num c + 1`. Moving up-right within a diagonal,
or to the start of the next diagonal at the top edge. -/
def nextCell : ℕ × ℕ → ℕ × ℕ
  | (n + 1, m) => (n, m + 1)
  | (0, m) => (m + 1, 0)
end

section
/-- The `k`-th triangular number `T(k) = k(k+1)/2`. -/
def tri (k : ℕ) : ℕ := k * (k + 1) / 2
end

section
/-- The pairing function `num n m = (n+m)(n+m+1)/2 + m` (Cantor's diagonal enumeration). -/
def num (n m : ℕ) : ℕ := tri (n + m) + m
end

section
/-- Its uncurried form, the actual `N × N → N` of the exercise. -/
def numP (p : ℕ × ℕ) : ℕ := num p.1 p.2
end

section
theorem num_succ_right (n m : ℕ) : num n (m + 1) = num (n + 1) m + 1 := by
  unfold num
  have h : n + (m + 1) = (n + 1) + m := by omega
  rw [h]; omega
end

section
theorem num_zero_zero : num 0 0 = 0 := rfl
end

section
/-- `k(k+1)` is even (choice-free, by induction). -/
theorem two_dvd_mul_succ (k : ℕ) : 2 ∣ k * (k + 1) := by
  induction k with
  | zero => exact ⟨0, by ring⟩
  | succ n ih =>
      obtain ⟨c, hc⟩ := ih
      refine ⟨c + (n + 1), ?_⟩
      have hexp : (n + 1) * (n + 1 + 1) = n * (n + 1) + 2 * (n + 1) := by ring
      rw [hexp, hc]; ring
end

section
/-- The defining doubling identity `2·T(k) = k(k+1)` — the division is exact because `k(k+1)` is
even. -/
theorem tri_mul_two (k : ℕ) : tri k * 2 = k * (k + 1) := by
  unfold tri
  exact Nat.div_mul_cancel (two_dvd_mul_succ k)
end

section
/-- The triangular recurrence `T(k+1) = T(k) + (k+1)`. -/
theorem tri_succ (k : ℕ) : tri (k + 1) = tri k + (k + 1) := by
  have e1 : tri k * 2 = k * (k + 1) := tri_mul_two k
  have e2 : tri (k + 1) * 2 = (k + 1) * (k + 1 + 1) := tri_mul_two (k + 1)
  have key : tri (k + 1) * 2 = (tri k + (k + 1)) * 2 := by
    have hexp : (tri k + (k + 1)) * 2 = tri k * 2 + (k + 1) * 2 := by ring
    rw [hexp, e1, e2]; ring
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) key
end

section
/-- The value `num n m` sits in the half-open diagonal block `[T(n+m), T(n+m+1))`: the upper bound. -/
theorem num_lt_tri_succ (n m : ℕ) : num n m < tri (n + m + 1) := by
  rw [tri_succ]; unfold num; omega
end

section
theorem num_succ_left (n : ℕ) : num (n + 1) 0 = num 0 n + 1 := by
  unfold num
  have h0 : (n + 1) + 0 = n + 1 := by omega
  have h1 : 0 + n = n := by omega
  rw [h0, h1, tri_succ]; omega
end

section
theorem numP_nextCell (c : ℕ × ℕ) : numP (nextCell c) = numP c + 1 := by
  obtain ⟨n, m⟩ := c
  cases n with
  | zero => exact num_succ_left m
  | succ k => exact num_succ_right k m
end

section
theorem tri_le_succ (k : ℕ) : tri k ≤ tri (k + 1) := by
  rw [tri_succ]; omega
end

section
/-- `T` is monotone (proved by hand on `≤` to stay choice-free). -/
theorem tri_mono {a b : ℕ} (h : a ≤ b) : tri a ≤ tri b := by
  induction h with
  | refl => exact le_refl _
  | step _ ih => exact le_trans ih (tri_le_succ _)
end

section
/-- **The function is one-one.** The diagonal `s = n+m` is recovered as the unique `s` with
`T(s) ≤ num n m < T(s+1)`; then `m` is the offset and `n = s - m`. -/
theorem num_injective : Function.Injective numP := by
  rintro ⟨n₁, m₁⟩ ⟨n₂, m₂⟩ h
  have h' : num n₁ m₁ = num n₂ m₂ := h
  have hs : n₁ + m₁ = n₂ + m₂ := by
    rcases lt_trichotomy (n₁ + m₁) (n₂ + m₂) with hlt | heq | hgt
    · exfalso
      have h1 : num n₁ m₁ < tri (n₁ + m₁ + 1) := num_lt_tri_succ n₁ m₁
      have h2 : tri (n₁ + m₁ + 1) ≤ tri (n₂ + m₂) := tri_mono (by omega)
      have h3 : tri (n₂ + m₂) ≤ num n₂ m₂ := by unfold num; omega
      omega
    · exact heq
    · exfalso
      have h1 : num n₂ m₂ < tri (n₂ + m₂ + 1) := num_lt_tri_succ n₂ m₂
      have h2 : tri (n₂ + m₂ + 1) ≤ tri (n₁ + m₁) := tri_mono (by omega)
      have h3 : tri (n₁ + m₁) ≤ num n₁ m₁ := by unfold num; omega
      omega
  have hbase : tri (n₁ + m₁) + m₁ = tri (n₂ + m₂) + m₂ := h'
  rw [hs] at hbase
  have hm : m₁ = m₂ := by omega
  have hn : n₁ = n₂ := by omega
  subst hm; subst hn; rfl
end

section
/-- The inverse `unnum v = nextCellᵛ (0, 0)`. -/
def unnum : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | v + 1 => nextCell (unnum v)
end

section
theorem numP_unnum (v : ℕ) : numP (unnum v) = v := by
  induction v with
  | zero => exact num_zero_zero
  | succ k ih =>
      show numP (nextCell (unnum k)) = k + 1
      rw [numP_nextCell, ih]
end

section
theorem unnum_numP (c : ℕ × ℕ) : unnum (numP c) = c :=
  num_injective (by rw [numP_unnum])
end

section
set_option linter.unusedVariables false

theorem example_513 : ∀ (c : Prod Nat Nat),
  @Eq (Prod Nat Nat)
    (DomainTheory.NeighbourhoodSystems.Exercise513.unnum (DomainTheory.NeighbourhoodSystems.Exercise513.numP c)) c :=
  DomainTheory.NeighbourhoodSystems.Exercise513.unnum_numP
end

end DomainTheory.NeighbourhoodSystems.Exercise513


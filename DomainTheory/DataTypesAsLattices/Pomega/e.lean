module

public import DomainTheory.DataTypesAsLattices.Pomega.Pomega
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.GroupWithZero.Nat
public import Aesop.BuiltinRules
public import Mathlib.Basic.Finite.Defs
import Mathlib.Data.Set.Finite.Basic

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def e (n : ℕ) : Pomega := {k | n.testBit k}

namespace e

private theorem pow2_eq (k : ℕ) : e (2 ^ k) = ({k} : Pomega) := by
  ext i
  simp [_root_.DomainTheory.DataTypesAsLattices.e, Nat.testBit_two_pow]

@[simp] theorem mem {n k : ℕ} : k ∈ e n ↔ n.testBit k := Iff.rfl

theorem zero : e 0 = ∅ := by
  ext k
  simp [_root_.DomainTheory.DataTypesAsLattices.e]

theorem pow2 (k : ℕ) : e (2 ^ k) = ({k} : Pomega) := pow2_eq k

theorem or (n m : ℕ) : e (n ||| m) = e n ∪ e m := by
  ext k
  simp [_root_.DomainTheory.DataTypesAsLattices.e, Nat.testBit_or]

theorem or_of_subset {n m : ℕ} {x : Pomega} (hn : e n ⊆ x) (hm : e m ⊆ x) : e (n ||| m) ⊆ x := by
  rw [or]
  exact Set.union_subset hn hm

theorem le_two_pow (k : ℕ) : k ≤ 2 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
    calc
      k + 1 ≤ 2 ^ k + 1 := Nat.succ_le_succ ih
      _ ≤ 2 ^ k + 2 ^ k := Nat.add_le_add_left Nat.one_le_two_pow _
      _ = 2 ^ k * 2 := (Nat.mul_two (2 ^ k)).symm
      _ = 2 ^ (k + 1) := (Nat.pow_succ 2 k).symm

theorem two_pow_le_of_testBit {n k : ℕ} (h : n.testBit k) : 2 ^ k ≤ n := by
  have hmod : (n >>> k) % 2 = 1 := by simpa [Nat.testBit] using h
  have hpos : 0 < n >>> k := Nat.pos_of_ne_zero fun hz => by simp [hz] at hmod
  have hdiv : 1 ≤ n / 2 ^ k := by
    rwa [Nat.shiftRight_eq_div_pow] at hpos
  simpa using (Nat.le_div_iff_mul_le (Nat.two_pow_pos k)).mp hdiv

theorem lt_two_pow' (k : ℕ) : k < 2 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
    calc
      k + 1 ≤ 2 ^ k := Nat.succ_le_of_lt ih
      _ < 2 ^ k + 2 ^ k := Nat.lt_add_of_pos_right (Nat.two_pow_pos k)
      _ = 2 ^ (k + 1) := by rw [← Nat.two_mul, Nat.mul_comm, Nat.pow_succ]

theorem mem_le {n k : ℕ} (h : k ∈ e n) : k ≤ n :=
  (le_two_pow k).trans (two_pow_le_of_testBit h)

theorem mem_lt {n k : ℕ} (h : k ∈ e n) : k < n := by
  have hle := mem_le h
  rcases eq_or_lt_of_le hle with rfl | hlt
  · exact (lt_irrefl k ((lt_two_pow' k).trans_le (two_pow_le_of_testBit h))).elim
  · exact hlt

theorem finite (n : ℕ) : (_root_.DomainTheory.DataTypesAsLattices.e n : Pomega).Finite :=
  (Finset.range (n + 1)).finite_toSet.subset fun _k hk =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (mem_le hk))

end e

end DomainTheory.DataTypesAsLattices

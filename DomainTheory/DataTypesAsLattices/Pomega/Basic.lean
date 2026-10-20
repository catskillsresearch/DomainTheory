/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
module

public import Mathlib.Data.Nat.Bitwise
import all Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Lattice.Bounded
import all Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
import all Mathlib.Data.Set.Lattice.Disjoint

@[expose] public section

/-!
# Scott 1976, §1 — the universal domain `Pω`

Ground truth: `sources/Data_Types_as_Lattices_vision.md`, pages 5–7.
-/

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, §1.** `Pω = {x | x ⊆ ω}`. -/
abbrev Pomega := Set ℕ

/-- **Scott 1976, after (2.2).** `⊥ = ∅`. -/
def botElem : Pomega := ∅

/-- **Scott 1976, after (2.2).** `⊤ = ω`. -/
def topElem : Pomega := Set.univ

@[simp] theorem mem_botElem (n : ℕ) : n ∈ botElem ↔ False := by simp [botElem]
@[simp] theorem mem_topElem (n : ℕ) : n ∈ topElem := Set.mem_univ n

/-- **Scott 1976, §1.** Finite set coded by the binary expansion of `n`. -/
def e (n : ℕ) : Pomega := {k | n.testBit k}

@[simp] theorem mem_e {n k : ℕ} : k ∈ e n ↔ n.testBit k := Iff.rfl

theorem two_pow_le_of_testBit {n k : ℕ} (h : n.testBit k) : 2 ^ k ≤ n := by
  have hmod : (n >>> k) % 2 = 1 := by simpa [Nat.testBit] using h
  have hpos : 0 < n >>> k := Nat.pos_of_ne_zero fun hz => by simp [hz] at hmod
  have hdiv : 1 ≤ n / 2 ^ k := by
    rwa [Nat.shiftRight_eq_div_pow] at hpos
  simpa using (Nat.le_div_iff_mul_le (Nat.two_pow_pos k)).mp hdiv

theorem le_two_pow (k : ℕ) : k ≤ 2 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
    calc
      k + 1 ≤ 2 ^ k + 1 := Nat.succ_le_succ ih
      _ ≤ 2 ^ k + 2 ^ k := Nat.add_le_add_left Nat.one_le_two_pow _
      _ = 2 ^ k * 2 := (Nat.mul_two (2 ^ k)).symm
      _ = 2 ^ (k + 1) := (Nat.pow_succ 2 k).symm

theorem mem_e_le {n k : ℕ} (h : k ∈ e n) : k ≤ n :=
  (le_two_pow k).trans (two_pow_le_of_testBit h)

instance (n k : ℕ) : Decidable (k ∈ e n) :=
  inferInstanceAs (Decidable (n.testBit k))

instance (n m : ℕ) : Decidable (e n ⊆ e m) :=
  decidable_of_iff (∀ k ≤ n, k ∈ e n → k ∈ e m) ⟨
    fun h k hk => h k (mem_e_le hk) hk,
    fun h _k _ hk => h hk⟩

/-- Finite pieces of `x` used in directed unions. -/
def eBelow (x : Pomega) (n : ℕ) : Pomega :=
  {k | e n ⊆ x ∧ k ∈ e n}

/-- Bit-mask code of a finite list of naturals. -/
def codeList : List ℕ → ℕ
  | [] => 0
  | k :: ks => 2 ^ k ||| codeList ks

noncomputable def codeFinset (s : Finset ℕ) : ℕ := codeList s.val.toList

/-- **Scott 1976, §1.** Diagonal pairing `(n, m) = ½(n+m)(n+m+1) + m`. -/
def pair (n m : ℕ) : ℕ := (n + m) * (n + m + 1) / 2 + m

def triangle (w : ℕ) : ℕ := w * (w + 1) / 2

theorem pair_eq_triangle (n m : ℕ) : pair n m = triangle (n + m) + m := rfl

theorem triangle_succ (w : ℕ) : triangle (w + 1) = triangle w + (w + 1) := by
  have hex : (w + 1) * (w + 2) = w * (w + 1) + 2 * (w + 1) := by
    calc
      (w + 1) * (w + 2) = (w + 1) * w + (w + 1) * 2 := Nat.mul_add _ _ _
      _ = w * (w + 1) + 2 * (w + 1) := by
        rw [Nat.mul_comm (w + 1) w, Nat.mul_comm (w + 1) 2]
  simp only [triangle]
  rw [show (w + 1) * ((w + 1) + 1) = (w + 1) * (w + 2) from rfl, hex]
  exact Nat.add_mul_div_left _ _ (by decide : 0 < 2)

theorem exists_triangle_bucket (k : ℕ) :
    ∃ w, triangle w ≤ k ∧ k < triangle (w + 1) := by
  let P := fun w : ℕ => k < triangle (w + 1)
  have hP : ∃ w, P w := ⟨k, by
    change k < triangle (k + 1)
    rw [triangle_succ]
    exact lt_of_lt_of_le (Nat.lt_succ_self k) (Nat.le_add_left (k + 1) _)⟩
  let w := Nat.find hP
  refine ⟨w, ?_, Nat.find_spec hP⟩
  cases hw : w with
  | zero => exact Nat.zero_le k
  | succ w' =>
    have hmin : ¬ P w' :=
      Nat.find_min hP (Nat.lt_of_succ_le (by
        have : w = Nat.find hP := rfl
        rw [← this, hw]))
    exact Nat.le_of_not_gt hmin

theorem exists_pair (k : ℕ) : ∃ n m, pair n m = k := by
  obtain ⟨w, hle, hlt⟩ := exists_triangle_bucket k
  refine ⟨w - (k - triangle w), k - triangle w, ?_⟩
  have hlt' : k < triangle w + w + 1 := by
    have : k < triangle w + (w + 1) := by rwa [triangle_succ] at hlt
    exact Nat.add_assoc (triangle w) w 1 ▸ this
  have hk : k ≤ triangle w + w := Nat.lt_succ_iff.mp hlt'
  have hm : k - triangle w ≤ w :=
    Nat.le_of_add_le_add_left ((Nat.add_sub_of_le hle).symm ▸ hk)
  have : w - (k - triangle w) + (k - triangle w) = w := Nat.sub_add_cancel hm
  rw [pair_eq_triangle, this, Nat.add_sub_of_le hle]

/-- Inverse of Cantor pairing. -/
noncomputable def unpair (k : ℕ) : ℕ × ℕ :=
  ((exists_pair k).choose, (exists_pair k).choose_spec.choose)
end DomainTheory.DataTypesAsLattices

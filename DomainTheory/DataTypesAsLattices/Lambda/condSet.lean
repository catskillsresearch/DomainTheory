module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Continuous.mem_scottUnion
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import Mathlib.Data.Nat.Bitwise

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def condSet (z x y : Pomega) : Pomega :=
  {n | n ∈ x ∧ 0 ∈ z} ∪ {m | m ∈ y ∧ ∃ k, k + 1 ∈ z}

namespace condSet

theorem bot (x y : Pomega) : condSet botElem x y = botElem := by
  ext n
  simp [condSet, botElem]

theorem ofNat_zero (x y : Pomega) : condSet (ofNat 0) x y = x := by
  ext n
  simp [condSet, ofNat]

theorem ofNat_one (x y : Pomega) : condSet (ofNat 1) x y = y := by
  ext n
  simp [condSet, ofNat]

theorem ofNat_succ (n : ℕ) (x y : Pomega) :
    condSet (ofNat (n + 1)) x y = y := by
  ext k
  simp [condSet, ofNat]

theorem same_bot (x : Pomega) : condSet botElem x x = botElem :=
  bot x x

theorem same_of_mem {z x : Pomega} {k : ℕ} (hk : k ∈ z) :
    condSet z x x = x := by
  ext n
  constructor
  · intro hn
    rcases hn with ⟨hnx, _⟩ | ⟨hnx, _⟩
    · exact hnx
    · exact hnx
  · intro hnx
    cases k with
    | zero => exact Or.inl ⟨hnx, hk⟩
    | succ t => exact Or.inr ⟨hnx, t, hk⟩

theorem same (z x : Pomega) (hz : z ≠ botElem) : condSet z x x = x := by
  obtain ⟨k, hk⟩ : ∃ k, k ∈ z := by
    by_contra h
    push Not at h
    exact hz (Set.ext fun n => by simp [botElem, h n])
  exact same_of_mem hk

theorem isScottContinuous_left (x y : Pomega) :
    IsScottContinuous (fun z => condSet z x y) := by
  constructor
  intro z
  ext k
  constructor
  · intro hk
    rcases hk with ⟨hkx, h0⟩ | ⟨hky, ⟨t, ht⟩⟩
    · have e1 : e 1 = ({0} : Pomega) := by simpa using e_pow2 0
      refine mem_scottUnion.mpr ⟨1, ?_, Or.inl ⟨hkx, ?_⟩⟩
      · simpa [e1, Set.singleton_subset_iff] using h0
      · simp [e1]
    · refine mem_scottUnion.mpr ⟨2 ^ (t + 1), ?_, Or.inr ⟨hky, t, ?_⟩⟩
      · simp [e_pow2, Set.singleton_subset_iff, ht]
      · simp [e_pow2]
  · intro hk
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp hk
    rcases hkm with ⟨hkx, h0⟩ | ⟨hky, ⟨t, ht⟩⟩
    · exact Or.inl ⟨hkx, hm h0⟩
    · exact Or.inr ⟨hky, t, hm ht⟩

theorem isScottContinuous_mid (z y : Pomega) :
    IsScottContinuous (fun x => condSet z x y) := by
  constructor
  intro x
  ext k
  constructor
  · intro hk
    rcases hk with ⟨hkx, h0⟩ | hky
    · refine mem_scottUnion.mpr ⟨2 ^ k, by simp [e_pow2, Set.singleton_subset_iff, hkx],
        Or.inl ⟨by simp [e_pow2], h0⟩⟩
    · refine mem_scottUnion.mpr ⟨0, by simp [e_zero], Or.inr hky⟩
  · intro hk
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp hk
    rcases hkm with ⟨hkx, h0⟩ | hky
    · exact Or.inl ⟨hm hkx, h0⟩
    · exact Or.inr hky

theorem isScottContinuous_right (z x : Pomega) :
    IsScottContinuous (fun y => condSet z x y) := by
  constructor
  intro y
  ext k
  constructor
  · intro hk
    rcases hk with hzx | ⟨hky, ht⟩
    · refine mem_scottUnion.mpr ⟨0, by simp [e_zero], Or.inl hzx⟩
    · refine mem_scottUnion.mpr ⟨2 ^ k, by simp [e_pow2, Set.singleton_subset_iff, hky],
        Or.inr ⟨by simp [e_pow2], ht⟩⟩
  · intro hk
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp hk
    rcases hkm with hzx | ⟨hky, ht⟩
    · exact Or.inl hzx
    · exact Or.inr ⟨hm hky, ht⟩

private theorem exists_pos_bit {n : ℕ} (hn : 2 ≤ n) :
    ∃ k, n.testBit (k + 1) = true := by
  by_contra hex
  push Not at hex
  have hfalse : ∀ k, n.testBit (k + 1) = false := fun k =>
    Bool.eq_false_iff.2 (hex k)
  have : n = 0 ∨ n = 1 := by
    cases h0 : n.testBit 0 with
    | false =>
      exact Or.inl <| Nat.zero_of_testBit_eq_false fun i => by
        cases i with
        | zero => exact h0
        | succ k => exact hfalse k
    | true =>
      exact Or.inr <| Nat.eq_of_testBit_eq fun i => by
        cases i with
        | zero => simp [h0]
        | succ k =>
          rw [hfalse k]
          exact (Nat.testBit_eq_false_of_lt
            (Nat.one_lt_two_pow (Nat.succ_ne_zero k))).symm
  omega

theorem e_iff (n0 n1 n2 m : ℕ) :
    m ∈ condSet (e n2) (e n0) (e n1) ↔
      (n0.testBit m = true ∧ n2.testBit 0 = true) ∨
        (n1.testBit m = true ∧ 2 ≤ n2) := by
  constructor
  · intro h
    rcases h with ⟨hm, h0⟩ | ⟨hm, ⟨k, hk⟩⟩
    · exact Or.inl ⟨mem_e.mp hm, mem_e.mp h0⟩
    · exact Or.inr ⟨mem_e.mp hm,
        (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
          (Nat.le_add_left 1 k) : (2 : ℕ) ^ 1 ≤ 2 ^ (k + 1)).trans
          (two_pow_le_of_testBit (mem_e.mp hk))⟩
  · intro h
    rcases h with ⟨hm, h0⟩ | ⟨hm, hn2⟩
    · exact Or.inl ⟨mem_e.mpr hm, mem_e.mpr h0⟩
    · obtain ⟨k, hk⟩ := exists_pos_bit hn2
      exact Or.inr ⟨mem_e.mpr hm, k, mem_e.mpr hk⟩

end condSet

end DomainTheory.DataTypesAsLattices

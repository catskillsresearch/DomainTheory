module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)
























/-- **`orUpTo`'s bit-by-bit characterization.** Bit `k` of `orUpTo n m N` is set exactly when some
`a < N` is a set bit of `n` with `a ≤ k` and `k - a` a set bit of `m`. -/
theorem testBit_orUpTo (n m : ℕ) : ∀ N k,
    (orUpTo n m N).testBit k = true ↔ ∃ a, a < N ∧ n.testBit a = true ∧ a ≤ k ∧ m.testBit (k - a) = true
  | 0, k => by simp [orUpTo]
  | N + 1, k => by
    show (myLor (orUpTo n m N) (selectFn (bitAt n N) (m <<< N) 0)).testBit k = true ↔ _
    rw [myLor_eq_lor, Nat.testBit_lor, Bool.or_eq_true, testBit_orUpTo n m N]
    by_cases hbit : n.testBit N = true
    · rw [(bitAt_eq_one_iff n N).mpr hbit, selectFn_one, Nat.testBit_shiftLeft]
      constructor
      · rintro (⟨a, haN, ha, hak, hb⟩ | h)
        · exact ⟨a, Nat.lt_succ_of_lt haN, ha, hak, hb⟩
        · rw [Bool.and_eq_true, decide_eq_true_iff] at h
          exact ⟨N, Nat.lt_succ_self N, hbit, h.1, h.2⟩
      · rintro ⟨a, haN1, ha, hak, hb⟩
        rcases (show a < N ∨ a = N by omega) with haN | haN
        · exact Or.inl ⟨a, haN, ha, hak, hb⟩
        · subst haN
          exact Or.inr (by rw [Bool.and_eq_true, decide_eq_true_iff]; exact ⟨hak, hb⟩)
    · have hne1 : bitAt n N ≠ 1 := fun h => hbit ((bitAt_eq_one_iff n N).mp h)
      have hle := bitAt_le_one n N
      have hnbit : bitAt n N = 0 := by omega
      rw [hnbit, selectFn_zero]
      simp only [Nat.zero_testBit, Bool.false_eq_true, or_false]
      constructor
      · rintro ⟨a, haN, ha, hak, hb⟩; exact ⟨a, Nat.lt_succ_of_lt haN, ha, hak, hb⟩
      · rintro ⟨a, haN1, ha, hak, hb⟩
        rcases (show a < N ∨ a = N by omega) with haN | haN
        · exact ⟨a, haN, ha, hak, hb⟩
        · subst haN; exact absurd ha hbit

end DomainTheory.NeighbourhoodSystems.Exercise723

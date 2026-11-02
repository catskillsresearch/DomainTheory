module

public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
import DomainTheory.DataTypesAsLattices.Continuous.mem_scottUnion
public import DomainTheory.DataTypesAsLattices.Lambda.Language

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def maxExtend (p : ℕ → Pomega) (x : Pomega) : Pomega :=
  {k | (x = ∅ ∧ ∀ n, k ∈ p n) ∨
    (∃ n, x = ofNat n ∧ k ∈ p n) ∨
    (x ≠ ∅ ∧ ∀ n, x ≠ ofNat n)}

def minExtend (p : ℕ → Pomega) (x : Pomega) : Pomega :=
  ⋃ n ∈ x, p n

theorem eq_2_1_empty (p : ℕ → Pomega) :
    maxExtend p botElem = ⋂ n, p n := by
  ext k
  constructor
  · intro hk
    rcases hk with ⟨_, hall⟩ | h | h
    · exact Set.mem_iInter.mpr hall
    · rcases h with ⟨n, hn, _⟩
      have : n ∈ (∅ : Pomega) := by
        have : (∅ : Pomega) = ofNat n := hn
        rw [this]; simp [ofNat]
      exact this.elim
    · exact (h.1 rfl).elim
  · intro hk
    exact Or.inl ⟨rfl, fun n => Set.mem_iInter.mp hk n⟩

theorem eq_2_1_singleton (p : ℕ → Pomega) (n : ℕ) :
    maxExtend p (ofNat n) = p n := by
  ext k
  constructor
  · intro hk
    rcases hk with ⟨he, _⟩ | ⟨m, hm, hkm⟩ | ⟨_, hall⟩
    · have hne : ofNat n ≠ ∅ := Set.Nonempty.ne_empty ⟨n, (rfl : n ∈ ofNat n)⟩
      exact (hne he).elim
    · have : n = m := by
        have hn : n ∈ ofNat m := hm ▸ (rfl : n ∈ ofNat n)
        simpa [ofNat] using hn
      subst this; exact hkm
    · exact (hall n rfl).elim
  · intro hk
    exact Or.inr (Or.inl ⟨n, rfl, hk⟩)

theorem eq_2_1_else (p : ℕ → Pomega) {x : Pomega}
    (hne : x ≠ botElem) (hsing : ∀ n, x ≠ ofNat n) :
    maxExtend p x = topElem := by
  ext k
  constructor
  · intro; trivial
  · intro
    exact Or.inr (Or.inr ⟨hne, hsing⟩)

namespace minExtend

theorem bot (p : ℕ → Pomega) : minExtend p botElem = botElem := by
  simp [minExtend, botElem]

theorem isScottContinuous (p : ℕ → Pomega) :
    IsScottContinuous (minExtend p) := by
  constructor
  intro x
  ext k
  constructor
  · intro hk
    obtain ⟨n, hn, hkn⟩ := Set.mem_iUnion₂.mp hk
    exact mem_scottUnion.mpr ⟨2 ^ n, by simp [e.pow2, Set.singleton_subset_iff, hn],
      by simp [minExtend, e.pow2, hkn]⟩
  · intro hk
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp hk
    obtain ⟨n, hn, hkn⟩ := Set.mem_iUnion₂.mp hkm
    exact Set.mem_iUnion₂.mpr ⟨n, hm hn, hkn⟩

theorem union (p : ℕ → Pomega) (x y : Pomega) :
    minExtend p (x ∪ y) = minExtend p x ∪ minExtend p y := by
  ext k
  simp [minExtend, or_and_right, exists_or]

end minExtend

end DomainTheory.DataTypesAsLattices

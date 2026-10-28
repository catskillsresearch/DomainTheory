module

public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Lambda.maxExtend
public import DomainTheory.DataTypesAsLattices.Lambda.mem_ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

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

end DomainTheory.DataTypesAsLattices

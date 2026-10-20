module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
import all Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace


























theorem oddEvenPack_eq_zero {f g : Pomega → Pomega} (x : Pomega) :
    oddEvenPack f g x = ofNat 0 ↔ f x = botElem ∧ g x = ofNat 0 := by
  constructor
  · intro h
    constructor
    · ext n
      constructor
      · intro hn
        have : 2 * n + 1 ∈ oddEvenPack f g x := Or.inl ⟨n, rfl, hn⟩
        rw [h] at this
        simp [ofNat] at this
      · intro hn
        exact ((mem_botElem n).mp hn).elim
    · ext n
      constructor
      · intro hn
        have hmem : 2 * n ∈ oddEvenPack f g x := Or.inr ⟨n, rfl, hn⟩
        rw [h] at hmem
        have : 2 * n = 0 := by simpa [ofNat] using hmem
        have hn0 : n = 0 := by
          have := Nat.mul_eq_zero.mp this
          exact this.resolve_left (by decide)
        simpa [ofNat] using hn0
      · intro hn
        simp [ofNat] at hn
        subst hn
        have : (0 : ℕ) ∈ oddEvenPack f g x := by rw [h]; simp [ofNat]
        rcases this with ⟨n, hk, _⟩ | ⟨n, hk, hn⟩
        · omega
        · have : n = 0 := by omega
          simpa [this] using hn
  · intro ⟨hf, hg⟩
    ext k
    constructor
    · intro hk
      rcases hk with ⟨n, hk, hn⟩ | ⟨n, hk, hn⟩
      · rw [hf] at hn; exact ((mem_botElem n).mp hn).elim
      · rw [hg] at hn; simp [ofNat] at hn; simp [ofNat, hk, hn]
    · intro hk
      simp [ofNat] at hk
      subst hk
      refine Or.inr ⟨0, rfl, ?_⟩
      rw [hg]; simp [ofNat]

end DomainTheory.DataTypesAsLattices

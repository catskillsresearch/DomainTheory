module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices



















































/-- The diagonal contradiction used in Scott 1976, Theorem 3.4. -/
theorem theorem_3_4_diagonal {val : ℕ → Pomega} {v : ℕ → ℕ} {b : Set ℕ}
    (hv : ∀ k, val (v k) = ofNat k ∩ val k)
    (hb : b = {j | val j = botElem})
    (hex : ∃ k, val k = {i | v i ∈ b}) : False := by
  obtain ⟨k, hk⟩ := hex
  have hiff : k ∈ val k ↔ v k ∈ b := by
    constructor
    · intro h
      have : k ∈ {i | v i ∈ b} := by rwa [hk] at h
      exact this
    · intro h
      have : k ∈ {i | v i ∈ b} := h
      rwa [← hk] at this
  have hinter : val (v k) = botElem ↔ k ∉ val k := by
    rw [hv]
    constructor
    · intro h hk'
      have this : k ∈ ofNat k ∩ val k := ⟨rfl, hk'⟩
      rw [h] at this
      exact this
    · intro h
      ext i
      constructor
      · intro ⟨hi, hval⟩
        simp [ofNat] at hi
        subst hi
        exact (h hval).elim
      · intro hi
        exact hi.elim
  have hbmem : v k ∈ b ↔ val (v k) = botElem := by
    rw [hb]; rfl
  have : k ∈ val k ↔ k ∉ val k :=
    hiff.trans (hbmem.trans hinter)
  by_cases hkmem : k ∈ val k
  · exact (this.mp hkmem) hkmem
  · exact hkmem (this.mpr hkmem)

end DomainTheory.DataTypesAsLattices

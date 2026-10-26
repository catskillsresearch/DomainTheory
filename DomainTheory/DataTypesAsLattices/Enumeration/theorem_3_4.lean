module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability.IsRE
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Retracts.comp
public import DomainTheory.DataTypesAsLattices.Enumeration.valNat
public import DomainTheory.DataTypesAsLattices.Enumeration.diagonalInterCode
public import DomainTheory.DataTypesAsLattices.Enumeration.theorem_3_2
public import DomainTheory.DataTypesAsLattices.Enumeration.primrec_diagonalInterCode
public import DomainTheory.DataTypesAsLattices.Computability.IsREu2ecombinatory
public import DomainTheory.DataTypesAsLattices.Enumeration.valNat_codes

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- The diagonal contradiction used in Scott 1976, Theorem 3.4. -/
theorem theorem_3_4.diagonal {val : ℕ → Pomega} {v : ℕ → ℕ} {b : Set ℕ}
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

/-- **Scott 1976, Theorem 3.4** for an r.e. undefined-index set. -/
theorem theorem_3_4.re_diagonal {val : ℕ → Pomega} {v : ℕ → ℕ}
    (hv : ∀ k, val (v k) = ofNat k ∩ val k)
    (_hRE : IsRE {j | val j = botElem})
    (hex : ∃ k, val k = {i | v i ∈ {j | val j = botElem}}) : False :=
  theorem_3_4.diagonal hv rfl hex

/-- **Scott 1976, Theorem 3.4 (The incompleteness theorem).**
The set of Gödel numbers denoting bottom is not recursively enumerable. -/
theorem theorem_3_4 :
    ¬ IsRE {n | valNat n = botElem} := by
  intro hb
  have hpre : IsRE {i | diagonalInterCode i ∈ {n | valNat n = botElem}} :=
    ⟨hb.out.comp primrec_diagonalInterCode.to_comp⟩
  obtain ⟨k, hk⟩ :=
    theorem_3_2.surjective (IsRE.combinatory hpre)
  exact theorem_3_4.diagonal (val := valNat) (v := diagonalInterCode)
    valNat.diagonalInterCode_eq rfl ⟨k, hk⟩

end DomainTheory.DataTypesAsLattices

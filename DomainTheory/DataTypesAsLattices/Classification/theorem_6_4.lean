/-ai
Scott's 𝔉 ∩ 𝔊 theorem (1976, Theorem 6.4) states that a set U is an intersection of a Scott-closed set and a Scott-open set if and only if U is the set of x at which some Scott-continuous f takes the value {0}.

If U is such an intersection C ∩ O, the odd-even packing of the top characteristic of the complement of C with the open characteristic of O is Scott continuous, and it equals {0} exactly when the first value is ⊥ and the second is {0}. Those conditions are membership in C and in O: the zero clause of the open characteristic records a finite piece already in O, and O is an upper set. Conversely, if U is the set of x with f(x) equal to {0}, take the set of x whose value is contained in {0} and the set of x with 0 in the value. The complement of the first is the union over k of the sets where k is nonzero and lies in the value. The summand for k = 0 is empty, and each remaining summand is a continuous preimage, so the complement is Scott open. The second set is Scott open by continuity of f, and the two sets meet in U.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
import all Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.Basic
public import DomainTheory.DataTypesAsLattices.Classification.oddEvenPack_eq_zero

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace


/-- **Scott 1976, Theorem 6.4 (The 𝔉 ∩̇ 𝔊 theorem).** -/
theorem theorem_6_4 :
    ∀ U, IsFcapG U ↔ ∃ f, IsScottContinuous f ∧ U = {x | f x = ofNat 0} := by
  intro U
  constructor
  · rintro ⟨C, O, hC, hO, rfl⟩
    refine ⟨oddEvenPack (charTop Cᶜ) (charOpen O),
      oddEvenPack_isScottContinuous (charTop_isScottContinuous Cᶜ)
        (charOpen_isScottContinuous O), ?_⟩
    ext x
    constructor
    · intro hx
      change oddEvenPack (charTop Cᶜ) (charOpen O) x = ofNat 0
      refine (oddEvenPack_eq_zero x).mpr ?_
      have hx' : x ∈ C ∧ x ∈ O := hx
      constructor
      · exact (charTop_eq_bot_of_closed hC x).mpr hx'.1
      · ext k
        constructor
        · intro ⟨hk0, n, hn, hne⟩
          simp [ofNat, hk0]
        · intro hk
          simp [ofNat] at hk
          subst hk
          obtain ⟨n, hn, hne⟩ := (mem_isScottOpen_iff hO).mp hx'.2
          exact ⟨rfl, n, hn, hne⟩
    · intro hf
      have hf' := (oddEvenPack_eq_zero (f := charTop Cᶜ) (g := charOpen O) x).mp hf
      constructor
      · exact (charTop_eq_bot_of_closed hC x).mp hf'.1
      · have : 0 ∈ charOpen O x := by rw [hf'.2]; simp [ofNat]
        obtain ⟨_, n, hn, hne⟩ := this
        exact isScottOpen_isUpper hO hne hn
  · rintro ⟨f, hf, rfl⟩
    refine ⟨{x | f x ⊆ ofNat 0}, {x | 0 ∈ f x}, ?_, mem_preimage_isScottOpen hf 0, ?_⟩
    · have : {x | f x ⊆ ofNat 0}ᶜ = ⋃ k : ℕ, {x | k ≠ 0 ∧ k ∈ f x} := by
        ext x
        constructor
        · intro hx
          have : ¬ f x ⊆ ofNat 0 := hx
          obtain ⟨k, hk, hk0⟩ := Set.not_subset.mp this
          refine Set.mem_iUnion.mpr ⟨k, ?_⟩
          simp [ofNat] at hk0
          exact ⟨hk0, hk⟩
        · intro hx
          obtain ⟨k, hk0, hk⟩ := Set.mem_iUnion.mp hx
          intro hsub
          exact hk0 (hsub hk)
      rw [this]
      exact isScottOpen_iUnion _ fun k => by
        by_cases hk0 : k = 0
        · subst hk0
          have : {x | (0 : ℕ) ≠ 0 ∧ 0 ∈ f x} = (∅ : Set Pomega) := by
            ext x; simp
          rw [this]; exact isScottOpen_empty
        · have : {x | k ≠ 0 ∧ k ∈ f x} = {x | k ∈ f x} := by
            ext x; simp [hk0]
          rw [this]; exact mem_preimage_isScottOpen hf k
    · ext x
      constructor
      · intro hx
        change f x ⊆ ofNat 0 ∧ 0 ∈ f x
        have hx' : f x = ofNat 0 := hx
        constructor
        · simp [hx']
        · simp [hx', ofNat]
      · intro hx
        change f x = ofNat 0
        ext n
        simp [ofNat]
        constructor
        · intro hn; exact hx.1 hn
        · intro hn; simpa [hn] using hx.2

end DomainTheory.DataTypesAsLattices


module

public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Continuous.isScottOpen_isUpper
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.oddEvenPack_eq_zero
public import DomainTheory.DataTypesAsLattices.Classification.IsFcapG
public import DomainTheory.DataTypesAsLattices.Classification.Basic

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

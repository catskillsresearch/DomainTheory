/-ai
Scott's 𝔉 ∩ 𝔊δ theorem (1976, Theorem 6.5) states that a set U is an intersection of a Scott-closed set and a Scott Gδ set if and only if U is the set of x at which some Scott-continuous f takes the value ⊤ + 1.

If U is C ∩ G with C Scott closed and G a Scott Gδ set, the 𝔊δ theorem supplies a Scott-continuous map equal to ⊤ exactly on G. Packing the top characteristic of the complement of C with that map is Scott continuous. At each x the characteristic is ⊥ or ⊤, and the packing equals ⊤ + 1 exactly when the characteristic is ⊥ and the second map equals ⊤, which is membership in C ∩ G. Conversely, if U is the set of x with f(x) equal to ⊤ + 1, take the set of x whose value is contained in ⊤ + 1 and the set of x whose value contains ⊤ + 1. The complement of the first equals the set of x with 0 in the value, because a number outside ⊤ + 1 must be 0 and 0 itself lies outside ⊤ + 1, and that set is Scott open. The second set is the intersection of the Scott-open sets of x with n + 1 in the value. The two sets meet in U.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
import all Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.Basic
public import DomainTheory.DataTypesAsLattices.Classification.theorem_6_3
public import DomainTheory.DataTypesAsLattices.Classification.fcapGdeltaPack_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Classification.zero_not_mem_succSet_top
public import DomainTheory.DataTypesAsLattices.Classification.fcapGdeltaPack_eq

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace


/-- **Scott 1976, Theorem 6.5 (The 𝔉 ∩̇ 𝔊_δ theorem).** -/
theorem theorem_6_5 :
    ∀ U, IsFcapGdelta U ↔
      ∃ f, IsScottContinuous f ∧ U = {x | f x = succSet topElem} := by
  intro U
  constructor
  · rintro ⟨C, G, hC, hG, rfl⟩
    obtain ⟨fG, hfG, rflG⟩ := (theorem_6_3 G).mp hG
    refine ⟨fcapGdeltaPack (charTop Cᶜ) fG,
      fcapGdeltaPack_isScottContinuous (charTop_isScottContinuous Cᶜ) hfG, ?_⟩
    ext x
    have hfval : charTop Cᶜ x = botElem ∨ charTop Cᶜ x = topElem := by
      by_cases hx : x ∈ C
      · exact Or.inl ((charTop_eq_bot_of_closed hC x).mpr hx)
      · exact Or.inr ((charTop_eq_top hC x).mpr hx)
    constructor
    · intro ⟨hxC, hxG⟩
      have hf : charTop Cᶜ x = botElem := (charTop_eq_bot_of_closed hC x).mpr hxC
      have hg : fG x = topElem := by rw [rflG] at hxG; exact hxG
      exact (fcapGdeltaPack_eq hfval).mpr ⟨hf, hg⟩
    · intro hpack
      obtain ⟨hf, hg⟩ := (fcapGdeltaPack_eq hfval).mp hpack
      exact ⟨(charTop_eq_bot_of_closed hC x).mp hf, by rw [rflG]; exact hg⟩
  · rintro ⟨f, hf, rfl⟩
    refine ⟨{x | f x ⊆ succSet topElem}, {x | succSet topElem ⊆ f x}, ?_, ?_, ?_⟩
    · have : {x | f x ⊆ succSet topElem}ᶜ = {x | 0 ∈ f x} := by
        ext x
        constructor
        · intro hx
          obtain ⟨k, hk, hknotin⟩ := Set.not_subset.mp hx
          have hk0 : k = 0 := by
            by_contra hne
            exact hknotin ⟨k - 1, Set.mem_univ _, (Nat.succ_pred_eq_of_ne_zero hne).symm⟩
          simpa [hk0] using hk
        · intro h0 hsub
          exact zero_not_mem_succSet_top (hsub h0)
      rw [this]
      exact mem_preimage_isScottOpen hf 0
    · refine ⟨fun n => {x | n + 1 ∈ f x}, fun n => mem_preimage_isScottOpen hf (n + 1), ?_⟩
      ext x
      constructor
      · intro hx
        exact Set.mem_iInter.mpr fun n => hx ⟨n, Set.mem_univ n, rfl⟩
      · intro hx k hk
        obtain ⟨n, _, rfl⟩ := hk
        exact Set.mem_iInter.mp hx n
    · ext x
      constructor
      · intro hx
        change f x ⊆ succSet topElem ∧ succSet topElem ⊆ f x
        have hx' : f x = succSet topElem := hx
        constructor <;> simp [hx']
      · intro hx
        change f x = succSet topElem
        exact subset_antisymm hx.1 hx.2

end DomainTheory.DataTypesAsLattices

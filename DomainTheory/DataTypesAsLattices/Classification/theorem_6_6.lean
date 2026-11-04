module

public import DomainTheory.DataTypesAsLattices.Classification.Classes
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
import DomainTheory.DataTypesAsLattices.Classification.BooleanMemE
import DomainTheory.DataTypesAsLattices.Continuous.IsScottOpen_more
import DomainTheory.DataTypesAsLattices.Continuous.isScottOpen_iff_isOpen
import Mathlib.Tactic.Bound.Init

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

theorem theorem_6_6 :
    ∀ U, U ∈ ScottB ↔
      ∃ f, IsScottContinuous f ∧ ∃ E : Set Pomega,
        E.Finite ∧ (∀ e ∈ E, e.Finite) ∧ U = {x | f x ∈ E} := by
  intro U
  constructor
  · intro hU
    have : BooleanMemE U := by
      induction hU with
      | ofOpen hU => exact BooleanMemE.ofOpen hU
      | union _ _ ihU ihV => exact BooleanMemE.union ihU ihV
      | inter _ _ ihU ihV => exact BooleanMemE.inter ihU ihV
      | compl _ ih => exact BooleanMemE.compl ih
    obtain ⟨f, N, E, hf, hfb, hEf, hEsub, rfl⟩ := this
    refine ⟨f, hf, E, hEf, fun e he => (BooleanMemE.finite_Iio N).subset (hEsub e he), rfl⟩
  · rintro ⟨f, hf, E, hE, hEfin, rfl⟩
    have : {x | f x ∈ E} = ⋃₀ ((fun e => {x | f x = e}) '' E) := by
      ext x
      constructor
      · intro hx
        exact ⟨{y | f y = f x}, ⟨f x, hx, rfl⟩, rfl⟩
      · intro hx
        obtain ⟨_, ⟨e, he, rfl⟩, hx'⟩ := hx
        have hxeq : f x = e := hx'
        change f x ∈ E
        rwa [hxeq]
    rw [this]
    refine IsBooleanOpen.sUnion_finite (hE.image _) fun W hW => ?_
    obtain ⟨e, heE, rfl⟩ := hW
    have hefin : e.Finite := hEfin e heE
    have hopen : IsScottOpen {x | e ⊆ f x} := by
      have : {x | e ⊆ f x} = ⋂ k ∈ hefin.toFinset, {x | k ∈ f x} := by
        ext x
        constructor
        · intro hx
          exact Set.mem_iInter₂.mpr fun k hk => hx (hefin.mem_toFinset.mp hk)
        · intro hx k hk
          exact Set.mem_iInter₂.mp hx k (hefin.mem_toFinset.mpr hk)
      rw [this, isScottOpen_iff_isOpen]
      exact isOpen_biInter_finset fun k _ =>
        (isScottOpen_iff_isOpen _).mp (IsScottContinuous.mem_preimage hf k)
    have hclosed : IsScottOpen {x | f x ⊆ e}ᶜ := by
      have : {x | f x ⊆ e}ᶜ = ⋃ k, {x | k ∉ e ∧ k ∈ f x} := by
        ext x
        constructor
        · intro hx
          obtain ⟨k, hk, hke⟩ := Set.not_subset.mp hx
          exact Set.mem_iUnion.mpr ⟨k, ⟨hke, hk⟩⟩
        · intro hx
          obtain ⟨k, hke, hk⟩ := Set.mem_iUnion.mp hx
          intro hsub
          exact hke (hsub hk)
      rw [this]
      exact IsScottOpen.iUnion _ fun k => by
        by_cases hke : k ∈ e
        · have : {x | k ∉ e ∧ k ∈ f x} = (∅ : Set Pomega) := by
            ext x; simp [hke]
          rw [this]; exact IsScottOpen.empty
        · have : {x | k ∉ e ∧ k ∈ f x} = {x | k ∈ f x} := by
            ext x; simp [hke]
          rw [this]; exact IsScottContinuous.mem_preimage hf k
    exact IsBooleanOpen.of_fcapG ⟨{x | f x ⊆ e}, {x | e ⊆ f x}, hclosed, hopen, by
      ext x
      constructor
      · intro hx
        have : f x = e := by
          have : f x ∈ ({e} : Set Pomega) := hx
          simpa using this
        exact ⟨this.subset, this.symm.subset⟩
      · intro hx
        have : f x = e := subset_antisymm hx.1 hx.2
        simp [this]⟩

end DomainTheory.DataTypesAsLattices

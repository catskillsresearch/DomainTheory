module

public import DomainTheory.DataTypesAsLattices.Continuous.scottUnion
public import DomainTheory.DataTypesAsLattices.Continuous.Basic
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottOpen_more
import DomainTheory.DataTypesAsLattices.Continuous.isOpen_memOpen
import DomainTheory.DataTypesAsLattices.Continuous.isScottOpen_iff_isOpen
import DomainTheory.DataTypesAsLattices.Continuous.isScottOpen_isUpper
import DomainTheory.DataTypesAsLattices.Continuous.mem_scottUnion
import Mathlib.Tactic.Bound.Init
import Mathlib.Data.Set.Finite.Basic

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

class IsScottContinuous (f : Pomega → Pomega) : Prop where
  out : ∀ x, f x = scottUnion f x

namespace IsScottContinuous

theorem monotone {f : Pomega → Pomega}
    (hf : IsScottContinuous f) {x y : Pomega} (h : x ⊆ y) : f x ⊆ f y := by
  intro m hm
  rw [hf.out x, mem_scottUnion] at hm
  rw [hf.out y, mem_scottUnion]
  obtain ⟨n, hn, hmn⟩ := hm
  exact ⟨n, subset_trans hn h, hmn⟩

theorem determined {f g : Pomega → Pomega}
    (hf : IsScottContinuous f) (hg : IsScottContinuous g)
    (hfin : ∀ n, f (e n) = g (e n)) : f = g := by
  funext x
  rw [hf.out x, hg.out x]
  simp [scottUnion, scottPiece, hfin]

theorem iff_continuous (f : Pomega → Pomega) :
    IsScottContinuous f ↔ Continuous f := by
  constructor
  · intro hf
    refine continuous_generateFrom_iff.2 ?_
    rintro _ ⟨k, rfl⟩
    rw [← isScottOpen_iff_isOpen]
    refine ⟨{n | k ∈ f (e n)}, ?_⟩
    ext x
    constructor
    · intro hx
      have : k ∈ scottUnion f x := by rwa [← hf.out x]
      obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp this
      exact Set.mem_iUnion₂.mpr ⟨n, hkn, hn⟩
    · intro hx
      obtain ⟨n, hkn, hn⟩ := Set.mem_iUnion₂.mp hx
      exact monotone hf hn hkn
  · intro hfcont
    constructor
    intro x
    ext k
    have hopen : IsScottOpen (f ⁻¹' memOpen k) :=
      (isScottOpen_iff_isOpen _).mpr (IsOpen.preimage hfcont (isOpen_memOpen k))
    constructor
    · intro hk
      obtain ⟨B, hB⟩ := hopen
      have hx : x ∈ ⋃ n ∈ B, basicNhhd n := by
        have : x ∈ f ⁻¹' memOpen k := hk
        rwa [hB] at this
      obtain ⟨n, hn, hxn⟩ := Set.mem_iUnion₂.mp hx
      have hen : k ∈ f (e n) := by
        have : e n ∈ f ⁻¹' memOpen k := by
          rw [hB]
          exact Set.mem_iUnion₂.mpr ⟨n, hn, (subset_rfl : e n ⊆ e n)⟩
        exact this
      exact mem_scottUnion.mpr ⟨n, hxn, hen⟩
    · intro hk
      obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp hk
      have : e n ∈ f ⁻¹' memOpen k := hkn
      exact isScottOpen_isUpper hopen this hn

theorem mem_preimage {f : Pomega → Pomega} (hf : IsScottContinuous f) (k : ℕ) :
    IsScottOpen {x | k ∈ f x} := by
  have : {x | k ∈ f x} = f ⁻¹' memOpen k := rfl
  rw [this, isScottOpen_iff_isOpen]
  exact IsOpen.preimage ((IsScottContinuous.iff_continuous f).mp hf) (isOpen_memOpen k)

theorem not_subset {f : Pomega → Pomega} (hf : IsScottContinuous f)
    (e : Pomega) : IsScottOpen {x | ¬ f x ⊆ e} := by
  have : {x | ¬ f x ⊆ e} = ⋃ k, {x | k ∉ e ∧ k ∈ f x} := by
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
      rw [this]; exact mem_preimage hf k

theorem subset_preimage {f : Pomega → Pomega} (hf : IsScottContinuous f)
    {e : Pomega} (he : e.Finite) : IsScottOpen {x | e ⊆ f x} := by
  have : {x | e ⊆ f x} = ⋂ k ∈ he.toFinset, {x | k ∈ f x} := by
    ext x
    constructor
    · intro hx
      exact Set.mem_iInter₂.mpr fun k hk => hx (he.mem_toFinset.mp hk)
    · intro hx k hk
      exact Set.mem_iInter₂.mp hx k (he.mem_toFinset.mpr hk)
  rw [this, isScottOpen_iff_isOpen]
  exact isOpen_biInter_finset fun k _ =>
    (isScottOpen_iff_isOpen _).mp (mem_preimage hf k)

theorem ne_eq_open_union_closed {f : Pomega → Pomega} (hf : IsScottContinuous f)
    {e : Pomega} (he : e.Finite) :
    {x | f x ≠ e} = {x | ¬ f x ⊆ e} ∪ {x | ¬ e ⊆ f x} ∧
      IsScottOpen {x | ¬ f x ⊆ e} ∧
      IsScottOpen {x | ¬ e ⊆ f x}ᶜ := by
  refine ⟨?_, not_subset hf e, ?_⟩
  · ext x
    constructor
    · intro hne
      by_cases hsub : f x ⊆ e
      · refine Or.inr fun hsup => hne (subset_antisymm hsub hsup)
      · exact Or.inl hsub
    · intro h heq
      rcases h with h | h
      · exact h heq.subset
      · exact h heq.symm.subset
  · have : {x | ¬ e ⊆ f x}ᶜ = {x | e ⊆ f x} := by
      ext x; simp
    rw [this]
    exact subset_preimage hf he

end IsScottContinuous

end DomainTheory.DataTypesAsLattices


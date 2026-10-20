module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableSplit
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableDiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableUnion
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx0_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx1_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateJunk_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateRemC_packStateC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateInnerC_packStateC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.mem_union_of_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xPseqAtomIdx
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xPseqAtomJunk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xPseqAtomJunk_zero_or_one
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xPseqAtomIdx_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.XFoldStep_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.XFold
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.XFold_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.XFold_succ
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.XFold_found_le_one
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.XFold_found_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.XFold_mem_of_found

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section XPseqCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hUnion1 : IsComputableUnion P₁)

include hD₁pos hD₁diff hD₁nomin in
/-- **The membership form of `XFold`'s correctness**: once a non-junk half-step atom has been found
below `N`, the running code's `P₁`-image is exactly the union of the genuine (non-junk) atoms seen
so far. Mirrors `yFold_mem_iff`, with `unionIdx_spec`'s conditional rewrite (discharged via
`XFold_mem_of_found`/`mem_union_of_mem`) in place of `unionUX`'s unconditional `UX_unionUX`. -/
theorem XFold_mem_iff (n : ℕ) :
    ∀ N, (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.1 = 1 →
      ∀ z : β, z ∈ P₁.X (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.2 ↔
        ∃ i < N, xPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i = 0 ∧
          z ∈ P₁.X (xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i) := by
  intro N
  induction N with
  | zero => intro h; simp [XFold_zero] at h
  | succ N ih =>
    intro hfound1 z
    rw [XFold_succ, XFoldStep_eq] at hfound1 ⊢
    rcases xPseqAtomJunk_zero_or_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n N with
      h0 | h1
    · rw [h0, selectFn_zero] at hfound1 ⊢
      have hle := XFold_found_le_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N
      rcases Nat.eq_zero_or_pos
          (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.1 with
        hf0 | hfpos
      · rw [show (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.1
          = 0 from hf0, selectFn_zero, unpair_pair_snd]
        constructor
        · intro hz; exact ⟨N, Nat.lt_succ_self N, h0, hz⟩
        · rintro ⟨i, hi, hie, hz⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
          · exact absurd ((XFold_found_iff P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
              hUnion1 n N).mpr ⟨i, hi', hie⟩) (by rw [hf0]; omega)
          · exact hz
      · have hf1 : (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.1
            = 1 := by omega
        rw [hf1, selectFn_one, unpair_pair_snd]
        have hprevmem := XFold_mem_of_found P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
          hD₁pos hD₁diff hD₁nomin hUnion1 n N hf1
        have hnewmem := xPseqAtomIdx_mem P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n N
        have hex : ∃ k, P₁.X k =
            P₁.X (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.2 ∪
              P₁.X (xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n N) :=
          P₁.surj (NeighborhoodSystem.mem_union_of_mem hD₁pos hD₁diff hD₁nomin hprevmem hnewmem)
        rw [hUnion1.unionIdx_spec hex, Set.mem_union, ih hf1 z]
        constructor
        · rintro (⟨i, hi, hie, hz⟩ | hz)
          · exact ⟨i, Nat.lt_succ_of_lt hi, hie, hz⟩
          · exact ⟨N, Nat.lt_succ_self N, h0, hz⟩
        · rintro ⟨i, hi, hie, hz⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
          · exact Or.inl ⟨i, hi', hie, hz⟩
          · exact Or.inr hz
    · rw [h1, selectFn_one] at hfound1 ⊢
      rw [ih hfound1 z]
      constructor
      · rintro ⟨i, hi, hie, hz⟩; exact ⟨i, Nat.lt_succ_of_lt hi, hie, hz⟩
      · rintro ⟨i, hi, hie, hz⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
        · exact ⟨i, hi', hie, hz⟩
        · exact absurd hie (by omega)

end XPseqCode

end DomainTheory.NeighbourhoodSystems

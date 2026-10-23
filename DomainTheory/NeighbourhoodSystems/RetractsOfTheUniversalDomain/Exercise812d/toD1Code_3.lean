module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.other_2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateRemC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.other
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.XPseqCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.toD1Code
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.domainIsoCode812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.part_c_2

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
namespace toD1Code

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section ToD1CodeRelIff

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)
  (hX0 : P₀.X 0 = D₀.master) (hY0 : P₁.X 0 = D₁.master)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 hX0 hY0 in
/-- **Exercise 8.12(d)(5)(f)(i).** `(ofIso domainIsoCode812d).rel` at raw indices reduces to a
single reindexed inclusion, exactly mirroring `Theorem88n.lean`'s `isoInj_rel_iff_incl`:
`ofIso`'s relation is `∃ _ : D₀.mem X, (e (D₀.principal ‹_›)).mem Y`; since `domainIsoCode812d`'s
`toFun` is literally `toD1Code …`, `(e (D₀.principal (P₀.mem_X n))).mem T` unfolds (via `toD1Code`'s
`mem` field and `mem_principal`) to `∃ k, T = P₁.X (XPseqCode … k) ∧ D₀.mem (P₀.X k) ∧ P₀.X n ⊆
P₀.X k`, and `D₀.mem (P₀.X k)` is always true (`P₀.mem_X k`), so it drops. -/
theorem rel_iff (n m : ℕ) :
    (ofIso (domainIsoCode812d P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
      hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0)).rel
      (P₀.X n) (P₁.X m) ↔
    ∃ k, P₁.X m = P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 k) ∧
      P₀.X n ⊆ P₀.X k := by
  show (∃ _ : D₀.mem (P₀.X n),
      (toD1Code P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff hD₀nomin hxSplit
        hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0
        (D₀.principal (P₀.mem_X n))).mem (P₁.X m)) ↔ _
  simp only [toD1Code, mem_principal]
  constructor
  · rintro ⟨-, k, hk, -, hsub⟩
    exact ⟨k, hk, hsub⟩
  · rintro ⟨k, hk, hsub⟩
    exact ⟨P₀.mem_X n, k, hk, P₀.mem_X k, hsub⟩

end ToD1CodeRelIff

end toD1Code
end DomainTheory.NeighbourhoodSystems

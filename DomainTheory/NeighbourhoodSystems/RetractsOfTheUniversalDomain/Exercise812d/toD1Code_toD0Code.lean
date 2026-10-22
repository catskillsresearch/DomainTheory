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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.XPseqCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.YPseqCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.XPseqCode_eq_Y_iff_X_eq_YPseqCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.toD1Code
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.toD0Code

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.mem_ne_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.union_mem_or_empty
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section ToD1CodeToD0Code

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
/-- **Exercise 8.12(d)(5)(e)(iii).** The `right_inv` content feeding `domainIsoCode812d`:
`toD1Code (toD0Code y) = y`, the exact mirror of `(e)(ii)`'s `toD0Code_toD1Code` with `P₀`/`P₁`,
`XPseqCode`/`YPseqCode` swapped throughout. Via `Element.ext`, unfolds to `∀ T, (∃ m n, T = P₁.X
(XPseqCode … m) ∧ P₀.X m = P₀.X (YPseqCode … n) ∧ y.mem (P₁.X n)) ↔ y.mem T`. Forward (`mp`, given
`⟨m, hT, n, hmn, hyn⟩`): `(d)(5)(c)(iii)`'s `XPseqCode_eq_Y_iff_X_eq_YPseqCode m n` applied
directly to `hmn` (no `.symm` needed here, unlike `toD0Code_toD1Code`'s forward direction — `hmn`'s
orientation already matches the lemma's RHS) gives `hYeq : P₁.X (XPseqCode … m) = P₁.X n`; `rw [hT,
hYeq]; exact hyn` closes it. Backward (`intro hyT`): `y.sub`/`P₁.surj` names `T` as some `P₁.X n`
(`subst`); witness `m := YPseqCode … n` handed over for free (`P₀.X m = P₀.X (YPseqCode … n)` is
`rfl`); the closing equation `T = P₁.X (XPseqCode … m)` (post-`subst`, `P₁.X n = P₁.X (XPseqCode …
(YPseqCode … n))`) needs `XPseqCode_eq_Y_iff_X_eq_YPseqCode (YPseqCode … n) n |>.mpr rfl`, then
**`.symm`** (unlike `toD0Code_toD1Code`'s backward direction, whose analogous closing equation
needed no `.symm` — the orientation asymmetry mirrors `toD1Code_up_mem`/`toD0Code_up_mem`'s own
`.symm`/no-`.symm` split). -/
theorem toD1Code_toD0Code (y : D₁.Element) :
    toD1Code P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff hD₀nomin hxSplit
      hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0
      (toD0Code P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff hD₀nomin hxSplit
        hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0 y) = y := by
  apply Element.ext
  intro T
  constructor
  · rintro ⟨m, hT, n, hmn, hyn⟩
    have hYeq : P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 m) =
        P₁.X n :=
      (XPseqCode_eq_Y_iff_X_eq_YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
        hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 m
        n).mpr hmn
    rw [hT, hYeq]
    exact hyn
  · intro hyT
    obtain ⟨n, hn⟩ := P₁.surj (y.sub hyT)
    subst hn
    exact ⟨YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n,
      ((XPseqCode_eq_Y_iff_X_eq_YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
        hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1
        (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n) n).mpr rfl).symm,
      n, rfl, hyT⟩

end ToD1CodeToD0Code

end DomainTheory.NeighbourhoodSystems

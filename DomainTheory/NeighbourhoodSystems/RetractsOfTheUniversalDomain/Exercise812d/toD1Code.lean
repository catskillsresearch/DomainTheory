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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.XPseqCode_mem_unconditional
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.XPseqCode_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.X_inter_eq_iff_XPseqCode_inter_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.toD1Code_up_mem

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section ToD1Code

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
  (hX0 : P₀.X 0 = D₀.master)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 hX0 in
/-- **Exercise 8.12(d)(5)(d)(ii).** `toD1Code : D₀.Element → D₁.Element`, the code-level pushforward
filter `{T | ∃ n, T = P₁.X (XPseqCode … n) ∧ x.mem (P₀.X n)}` — generalizes `Exercise812c.lean`'s
`toD1` ((c)(vii)(4)). `sub` cites `(d)(4)`'s `XPseqCode_mem_unconditional` directly; `master_mem`
cites `(d)(5)(a)`'s `XPseqCode_zero` at the witness `n = 0`, using `hX0` to identify `P₀.X 0` with
`D₀.master`. `inter_mem` needs **no** covering search (unlike `toD1`'s `exists_inter_index_X`):
given `hxi : x.mem (P₀.X i)`/`hxj : x.mem (P₀.X j)`, `x.inter_mem hxi hxj`/`x.sub` shows
`P₀.X i ∩ P₀.X j` is already `D₀`-genuine, so `P₀.surj` names it as some `P₀.X m` outright,
`P₀.inter_spec` reads this off as the closed-form index equation `P₀.X (P₀.inter i j) = P₀.X i ∩
P₀.X j`, and `(d)(5)(b)(iv)`'s `X_inter_eq_iff_XPseqCode_inter_eq` transports the same equation
across to `XPseqCode`, so `P₀.inter i j` is directly the witness index needed. `up_mem` is exactly
`(d)(5)(d)(i)`'s `toD1Code_up_mem`. -/
def toD1Code (x : D₀.Element) : D₁.Element where
  mem T := ∃ n, T = P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n) ∧
    x.mem (P₀.X n)
  sub := fun ⟨n, hn, _⟩ =>
    hn ▸ XPseqCode_mem_unconditional P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
      hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion1 n
  master_mem := ⟨0, (XPseqCode_zero P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
    hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion1 hX0).symm,
    by rw [hX0]; exact x.master_mem⟩
  inter_mem := by
    rintro T1 T2 ⟨i, rfl, hxi⟩ ⟨j, rfl, hxj⟩
    have hDmem : D₀.mem (P₀.X i ∩ P₀.X j) := x.sub (x.inter_mem hxi hxj)
    obtain ⟨m, hm⟩ := P₀.surj hDmem
    have hcons : ∃ k, P₀.X k ⊆ P₀.X i ∩ P₀.X j := ⟨m, hm.le⟩
    have hinterEq : P₀.X (P₀.inter i j) = P₀.X i ∩ P₀.X j := P₀.inter_spec hcons
    refine ⟨P₀.inter i j, ?_, ?_⟩
    · exact (X_inter_eq_iff_XPseqCode_inter_eq P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
        hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
        hUnion1 i j (P₀.inter i j)).mp hinterEq.symm
    · rw [hinterEq]; exact x.inter_mem hxi hxj
  up_mem := toD1Code_up_mem P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
    hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 x

end ToD1Code

end DomainTheory.NeighbourhoodSystems

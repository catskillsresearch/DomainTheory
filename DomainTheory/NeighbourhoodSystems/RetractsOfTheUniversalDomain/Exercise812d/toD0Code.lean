module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.other_2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateRemC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.other
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.XPseqCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.YPseqCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.YPseqCode_2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.XPseqCode_2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.part_c_2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.union
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.toD1Code

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
namespace toD0Code

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section ToD0CodeUpMem

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

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 in
/-- **Exercise 8.12(d)(5)(d)(iii).** The standalone `up_mem` obligation for `toD0Code`'s membership
predicate `fun S => ∃ n, S = P₀.X (YPseqCode … n) ∧ y.mem (P₁.X n)`, the exact mirror of
`(d)(5)(d)(i)`'s `toD1Code.up_mem` for the `D₁ → D₀` direction: destructure `h1` as `⟨i, rfl, hyi⟩`;
`P₀.surj` names the arbitrary target `S2` as some `P₀.X k`; `(d)(5)(c)(ii)`'s
`YPseqCode.subset_X_iff_Y_subset_XPseqCode` turns `hS1S2 : P₀.X (YPseqCode … i) ⊆ P₀.X k` into
`P₁.X i ⊆ P₁.X (XPseqCode … k)`; `y.up_mem hyi (XPseqCode.mem_unconditional k) this` gives
`y.mem (P₁.X (XPseqCode … k))` — already literally `y.mem (P₁.X j)` for the explicit witness
`j := XPseqCode … k`, no covering search needed; `(d)(5)(c)(iii)`'s
`XPseqCode.eq_Y_iff_X_eq_YPseqCode`, applied at the self-referential pair `(k, XPseqCode … k)`
whose "other side" is `rfl`, supplies the closing index equation `P₀.X k = P₀.X (YPseqCode …
(XPseqCode … k))` for free — note no `.symm` is needed here, unlike `toD1Code.up_mem`, since the
goal orientation already matches `XPseqCode.eq_Y_iff_X_eq_YPseqCode`'s `.mp` output directly. -/
theorem up_mem (y : D₁.Element) {S1 S2 : Set α}
    (h1 : ∃ n, S1 = P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n) ∧
      y.mem (P₁.X n))
    (hD0S2 : D₀.mem S2) (hS1S2 : S1 ⊆ S2) :
    ∃ n, S2 = P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n) ∧
      y.mem (P₁.X n) := by
  obtain ⟨i, rfl, hyi⟩ := h1
  obtain ⟨k, hk⟩ := P₀.surj hD0S2
  subst hk
  have hsub : P₁.X i ⊆
      P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 k) :=
    (YPseqCode.subset_X_iff_Y_subset_XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1
      i k).mp hS1S2
  have hyXk :
      y.mem (P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 k)) :=
    y.up_mem hyi
      (XPseqCode.mem_unconditional P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
        hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion1 k)
      hsub
  refine ⟨XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 k, ?_, hyXk⟩
  exact (XPseqCode.eq_Y_iff_X_eq_YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
    hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1
    k (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 k)).mp rfl

end ToD0CodeUpMem

end toD0Code
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section ToD0Code

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
/-- **Exercise 8.12(d)(5)(d)(iv).** `toD0Code : D₁.Element → D₀.Element`, the code-level pullback
filter `{S | ∃ n, S = P₀.X (YPseqCode … n) ∧ y.mem (P₁.X n)}` — exact mirror of `(d)(5)(d)(ii)`'s
`toD1Code` for the `D₁ → D₀` direction. `sub` cites `(d)(4)`'s `YPseqCode.mem_unconditional`
directly; `master_mem` cites `(d)(5)(a)`'s `YPseqCode.zero` at the witness `n = 0`, using `hY0` to
identify `P₁.X 0` with `D₁.master`. `inter_mem` mirrors `toD1Code`'s corrected version exactly, with
the roles of `P₀`/`P₁` swapped: given `hyi : y.mem (P₁.X i)`/`hyj : y.mem (P₁.X j)`, `y.inter_mem`/
`y.sub` shows `P₁.X i ∩ P₁.X j` is already `D₁`-genuine, so `P₁.surj` names it as some `P₁.X m`
outright, `P₁.inter_spec` reads this off as the closed-form index equation `P₁.X (P₁.inter i j) =
P₁.X i ∩ P₁.X j`, and `(d)(5)(b)(iv)`'s `YPseqCode.inter_eq_iff_Y_inter_eq` transports the same
equation across to `YPseqCode`, so `P₁.inter i j` is directly the witness index needed (**note the
iff's orientation is reversed relative to `X_inter_eq_iff_XPseqCode_inter_eq`**: `YPseqCode`-stuff is
on the *left*, so this uses `.mpr` with `hinterEq.symm`, not `.mp` with `hinterEq` as `toD1Code`
did). `up_mem` is exactly `(d)(5)(d)(iii)`'s `toD0Code.up_mem`. -/
def toD0Code (y : D₁.Element) : D₀.Element where
  mem S := ∃ n, S = P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n) ∧
    y.mem (P₁.X n)
  sub := fun ⟨n, hn, _⟩ =>
    hn ▸ YPseqCode.mem_unconditional P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
      hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 n
  master_mem := ⟨0, (YPseqCode.zero P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
    hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hX0 hY0).symm,
    by rw [hY0]; exact y.master_mem⟩
  inter_mem := by
    rintro S1 S2 ⟨i, rfl, hyi⟩ ⟨j, rfl, hyj⟩
    have hDmem : D₁.mem (P₁.X i ∩ P₁.X j) := y.sub (y.inter_mem hyi hyj)
    obtain ⟨m, hm⟩ := P₁.surj hDmem
    have hcons : ∃ k, P₁.X k ⊆ P₁.X i ∩ P₁.X j := ⟨m, hm.le⟩
    have hinterEq : P₁.X (P₁.inter i j) = P₁.X i ∩ P₁.X j := P₁.inter_spec hcons
    refine ⟨P₁.inter i j, ?_, ?_⟩
    · exact (YPseqCode.inter_eq_iff_Y_inter_eq P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
        hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
        hUnion1 i j (P₁.inter i j)).mpr hinterEq.symm
    · rw [hinterEq]; exact y.inter_mem hyi hyj
  up_mem := toD0Code.up_mem P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
    hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 y

end ToD0Code

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace toD0Code

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section ToD0CodeToD1Code

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
/-- **Exercise 8.12(d)(5)(e)(ii).** The `left_inv` content feeding `domainIsoCode812d`:
`toD0Code (toD1Code x) = x`. Via `Element.ext`, unfolds to `∀ S, (∃ m n, S = P₀.X (YPseqCode …
m) ∧ P₁.X m = P₁.X (XPseqCode … n) ∧ x.mem (P₀.X n)) ↔ x.mem S`. Forward (`mp`): given the witness
`⟨m, hS, n, hmn, hxn⟩`, `(d)(5)(c)(iii)`'s `XPseqCode.eq_Y_iff_X_eq_YPseqCode n m` transports
`hmn.symm` into `hXeq : P₀.X n = P₀.X (YPseqCode … m)`; `rw [hS, ← hXeq]` reduces the goal `x.mem
S` to `x.mem (P₀.X n)`, closed by `hxn`. Backward (`mpr`): given `hxS : x.mem S`, `x.sub`/`P₀.surj`
names `S` as some `P₀.X n` outright (`subst`); take `m := XPseqCode … n` (handed over for free, no
search — `P₁.X m = P₁.X (XPseqCode … n)` is `rfl`); the closing equation `P₀.X n = P₀.X (YPseqCode
… m)` is `XPseqCode.eq_Y_iff_X_eq_YPseqCode n (XPseqCode … n) |>.mp rfl` applied at the
self-referential pair `(n, XPseqCode … n)`, exactly `toD1Code.up_mem`'s pattern — no
`hXcover`/`hYcover`-style double search needed, unlike `domainIso812c.left_inv`'s own proof. -/
theorem toD1Code (x : D₀.Element) :
    toD0Code P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff hD₀nomin hxSplit
      hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0
      (_root_.DomainTheory.NeighbourhoodSystems.toD1Code P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff hD₀nomin hxSplit
        hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0 x) = x := by
  apply Element.ext
  intro S
  constructor
  · rintro ⟨m, hS, n, hmn, hxn⟩
    have hXeq : P₀.X n =
        P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 m) :=
      (XPseqCode.eq_Y_iff_X_eq_YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
        hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 n
        m).mp hmn.symm
    rw [hS, ← hXeq]
    exact hxn
  · intro hxS
    obtain ⟨n, hn⟩ := P₀.surj (x.sub hxS)
    subst hn
    exact ⟨XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n,
      (XPseqCode.eq_Y_iff_X_eq_YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
        hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 n
        (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n)).mp rfl,
      n, rfl, hxS⟩

end ToD0CodeToD1Code

end toD0Code
end DomainTheory.NeighbourhoodSystems

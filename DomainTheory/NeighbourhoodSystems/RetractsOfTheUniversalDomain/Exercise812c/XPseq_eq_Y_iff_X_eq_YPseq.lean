/-ai
XPseq j equals the enumerated set Y k if and only if the enumerated set X j equals YPseq k.

If the first equality holds, the two cross-inclusion facts give both inclusions between X j and YPseq k. If the second equality holds, the same two facts in the other direction give both inclusions between XPseq j and Y k. Each pair of inclusions is antisymmetry.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.XPseq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.YPseq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.X_subset_YPseq_iff_XPseq_subset_Y
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.YPseq_subset_X_iff_Y_subset_XPseq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.NoMinimal
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.DiffClosed

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.IsEffectivelyGiven
@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

section Iso

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hXcover : ∀ S, D₀.mem S ↔ ∃ n, S = X n) (hYcover : ∀ S, D₁.mem S ↔ ∃ n, S = Y n)
  (hX0 : X 0 = D₀.master) (hY0 : Y 0 = D₁.master)

include hD₀pos hD₀diff hD₁pos hD₁diff hXmem hYmem hD₀mne hD₁mne in
/-- **Exercise 8.12(c)(vii)(4), the cross-parity `embed_eq_iff` analogue.** `XPseq j = Y k ↔
X j = YPseq k`: unlike `Theorem88a.lean`'s single-enumeration `embed_eq_iff` (a direct corollary of
one `embed_subset_iff` applied twice), this two-family version packages **both** cross-parity order
facts from (vii)(3) (`X_subset_YPseq_iff_XPseq_subset_Y` at `(j, k)` and
`YPseq_subset_X_iff_Y_subset_XPseq` at `(k, j)`) via antisymmetry on each side. Needed because
`toD1`/`toD0`'s `up_mem` case must rename a `D₁`-mem (resp. `D₀`-mem) witness produced by
`hYcover`/`hXcover` as some `Y k`/`X k` back into the `XPseq`/`YPseq` "coordinates" that the filter
`x`/`y` actually testifies about. -/
theorem XPseq_eq_Y_iff_X_eq_YPseq (j k : ℕ) :
    XPseq D₀ D₁ hD₀nomin hD₁nomin X Y j = Y k ↔ X j = YPseq D₀ D₁ hD₀nomin hD₁nomin X Y k := by
  constructor
  · intro h
    exact Set.Subset.antisymm
      ((X_subset_YPseq_iff_XPseq_subset_Y D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y
        hXmem hYmem hD₀mne hD₁mne j k).mpr h.subset)
      ((YPseq_subset_X_iff_Y_subset_XPseq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y
        hXmem hYmem hD₀mne hD₁mne k j).mpr h.symm.subset)
  · intro h
    exact Set.Subset.antisymm
      ((X_subset_YPseq_iff_XPseq_subset_Y D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y
        hXmem hYmem hD₀mne hD₁mne j k).mp h.subset)
      ((YPseq_subset_X_iff_Y_subset_XPseq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y
        hXmem hYmem hD₀mne hD₁mne k j).mp h.symm.subset)

end Iso

end DomainTheory.NeighbourhoodSystems

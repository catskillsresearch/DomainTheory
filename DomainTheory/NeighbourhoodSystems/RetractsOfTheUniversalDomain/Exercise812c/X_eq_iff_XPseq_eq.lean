module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.XPseq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.X_subset_iff_XPseq_subset
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.NoMinimal
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.DiffClosed

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
/-- **Exercise 8.12(c)(vii)(6), the same-family `embed_eq_iff` companion.** `X i = X j ↔
XPseq i = XPseq j`, needed by `domainIso812c`'s `map_rel_iff'`. Unlike `up_mem`'s two-*family* renaming
(needing (4)'s `XPseq_eq_Y_iff_X_eq_YPseq`), `map_rel_iff'` only ever compares two `XPseq`-indices
against each other, so the ordinary same-family pattern — `X_subset_iff_XPseq_subset` applied in
each direction, packaged via `Set.Subset.antisymm` — suffices, exactly as `Theorem88a.lean`'s own
`embed_eq_iff` (single index family). -/
theorem X_eq_iff_XPseq_eq (i j : ℕ) :
    X i = X j ↔ XPseq D₀ D₁ hD₀nomin hD₁nomin X Y i = XPseq D₀ D₁ hD₀nomin hD₁nomin X Y j := by
  constructor
  · intro h
    exact Set.Subset.antisymm
      ((X_subset_iff_XPseq_subset D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
        hYmem hD₀mne hD₁mne i j).mp h.subset)
      ((X_subset_iff_XPseq_subset D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
        hYmem hD₀mne hD₁mne j i).mp h.symm.subset)
  · intro h
    exact Set.Subset.antisymm
      ((X_subset_iff_XPseq_subset D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
        hYmem hD₀mne hD₁mne i j).mpr h.subset)
      ((X_subset_iff_XPseq_subset D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
        hYmem hD₀mne hD₁mne j i).mpr h.symm.subset)

end Iso

end DomainTheory.NeighbourhoodSystems

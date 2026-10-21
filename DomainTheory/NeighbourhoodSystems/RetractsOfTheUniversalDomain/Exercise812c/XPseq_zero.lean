/-ai
XPseq at stage 0 equals the master of the second system.

The forward inclusion is the general containment of XPseq in that master. For the reverse, the two masters are empty together, and the master of the second system is a neighbourhood. Splitting it against X 0, whose difference from the master of the first system is empty by the convention that X 0 is that master, forces the second output of the split to be empty. The two outputs union to the master, so the first output is the master. That output is the second component of the positive X-step on the two masters, and the empty sign sequence includes it in XPseq 0.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.splitChoice'
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.splitChoice'_isSplitSpec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.xStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.XPseq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.subset_XPseq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.XPseq_subset_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.NoMinimal
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.DiffClosed

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.IsEffectivelyGiven
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.V_no_minimal
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCode_disjoint_YseqCode_of_posTwin_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCode_succ_true
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.hcoreIdxYc
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.transfer_dir_idxYc
@[expose] public section

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

include hD₀pos hD₀diff hD₁pos hD₁diff hXmem hYmem hD₀mne hD₁mne hX0 in
/-- **Exercise 8.12(c)(vii)(2).** `XPseq 0 = D₁.master` (Scott's `X 0 = D₀.master`/`Y 0 = D₁.master`
convention transfers to `atomPair`'s `D₁`-side image), mirroring `Theorem88.lean`'s
`Yseq_zero_eq_master`: unfolding one step of the two-sided recursion at `n = 0`, `atomPair`'s own
`0`-clause is `(D₀.master, D₁.master)` regardless of the sign sequence, so the `X`-sub-step's split
against `X 0 = D₀.master` puts everything into the "+"-branch on both outputs (the "−"-branch
`D₀.master \ D₀.master = ∅` is forced empty by `SplitSpec'`), and `I ∪ J = D₁.master` with `J = ∅`
forces `I = D₁.master`. -/
theorem XPseq_zero : XPseq D₀ D₁ hD₀nomin hD₁nomin X Y 0 = D₁.master := by
  apply Set.Subset.antisymm
    (XPseq_subset_master D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem
      hD₀mne hD₁mne 0)
  have hAB1 : D₀.master = ∅ ↔ D₁.master = ∅ :=
    ⟨fun h => absurd h hD₀mne.ne_empty, fun h => absurd h hD₁mne.ne_empty⟩
  have hBE1 : D₁.master = ∅ ∨ D₁.mem D₁.master := Or.inr D₁.master_mem
  have hspec1 := splitChoice'_isSplitSpec D₁ hD₁nomin hAB1 hBE1 (X 0)
  have hdiff1 : D₀.master \ X 0 = ∅ := by rw [hX0]; exact Set.sdiff_self
  have h2empty1 : (splitChoice' D₁ hD₁nomin D₀.master D₁.master (X 0)).2 = ∅ :=
    hspec1.2.2.2.1.mp hdiff1
  have hunion1 := hspec1.2.2.2.2.1
  rw [h2empty1, Set.union_empty] at hunion1
  have hkey : D₁.master ⊆ (xStep D₁ hD₁nomin D₀.master D₁.master (X 0) true).2 := by
    show D₁.master ⊆ (splitChoice' D₁ hD₁nomin D₀.master D₁.master (X 0)).1
    rw [hunion1]
  exact hkey.trans (subset_XPseq D₀ D₁ hD₀nomin hD₁nomin X Y (Fin.elim0 : Fin 0 → Bool × Bool))

end Iso

end DomainTheory.NeighbourhoodSystems

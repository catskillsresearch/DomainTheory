module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.xyStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.inter_diff_eq_diff_of_subset
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.genAtom_succ'
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.yStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.xStep_snd_subset
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.atomPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.atomPair_succ_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.atomPair_invariant
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.atomPair_snd_subset_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.combinedY
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.combinedδ
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.combinedY_odd
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.combinedδ_odd
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.genAtom_combinedY_succ_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.NoMinimal
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.DiffClosed

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.IsEffectivelyGiven
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtomDecidable.DAtom_eq_empty_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.V_no_minimal
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCode_disjoint_YseqCode_of_posTwin_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCode_succ_true
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.hcoreIdxYc
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.transfer_dir_idxYc
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

/-- **Headline closed form, `β`-side** (Exercise 8.12(c)(vi)(5)(b)), symmetric to
`atomPair_fst_eq_genAtom`: `atomPair δ n`'s `β`-side coincides with `genAtom` over the interleaved
family `combinedY` at depth `2 * n`, via `genAtom_combinedY_succ_eq` ((vi)(5)(a)'s `X`-sub-step
closed form `xStep_snd_succ_eq`) then the `Y`-sub-step's direct `β`-side output (elementary, no
closed form needed — it is literally `if (δ n).2 then B1 ∩ Y n else B1 \ Y n` by `yStep`'s own
definition). -/
theorem atomPair_snd_eq_genAtom (δ : ℕ → Bool × Bool) (n : ℕ) :
    (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 =
      genAtom (combinedY D₀ D₁ hD₀nomin hD₁nomin X Y) D₁.master (combinedδ δ) (2 * n) := by
  induction n with
  | zero => rfl
  | succ n hIH =>
      have hodd := genAtom_combinedY_succ_eq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin
        X Y hXmem hYmem hD₀mne hD₁mne δ n hIH
      have h2 : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
      rw [atomPair_succ_eq, h2, genAtom_succ', combinedδ_odd, combinedY_odd, hodd]
      obtain ⟨hAB, -, hBmem⟩ := atomPair_invariant D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff
        hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne δ n
      have hB1sub := (xStep_snd_subset hD₁nomin hAB hBmem (X n) (δ n).1).trans
        (atomPair_snd_subset_master D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
          hYmem hD₀mne hD₁mne δ n)
      simp only [yStep, xyStep, Prod.swap]
      rcases Bool.eq_false_or_eq_true (δ n).2 with hb | hb
      · simp only [hb, ite_true]
      · simp only [hb, Bool.false_eq_true, ite_false]
        exact (inter_diff_eq_diff_of_subset hB1sub).symm

end AtomPair

end DomainTheory.NeighbourhoodSystems

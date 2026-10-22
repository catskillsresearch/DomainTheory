module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.splitChoice'_isSplitSpec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.xyStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.xStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.yStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.xStep_fst_subset
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.atomPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.xStep_spec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.atomPair_fst_subset_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.YPseq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.yStep_fst_eq_inter_YPseq
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

/-- **Two-branch closed form for the `Y`-sub-step's `D₀`-side output** (Exercise 8.12(c)(vi)(5)(a)):
completes `yStep_fst_eq_inter_YPseq`'s `true`-only I-formula into a full `genAtom`-shaped recursive
step at *either* sign of the `Y`-sub-step itself (the `X`-sub-step's own bit stays fixed at `(δ
n).1`, exactly as in `yStep_fst_eq_inter_YPseq` — no `xStep_spec_bit`-style further generalization
is needed here, since 8.12(c)(vi)(5)(b)'s combined-family recursion only ever calls this at `δ`'s
own bit). Mirrors `xStep_snd_succ_eq` above (equivalently `Theorem88.lean`'s `atomU_succ_eq`), with
the `false` branch derived algebraically from the `true` branch plus `SplitSpec'`'s `I ∪ J = B`/
`I ∩ J = ∅`. -/
theorem yStep_fst_succ_eq (δ : ℕ → Bool × Bool) (n : ℕ) (b : Bool) :
    (yStep D₀ hD₀nomin
        (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
          (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) (δ n).1).1
        (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
          (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) (δ n).1).2
        (Y n) b).1 =
      (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
          (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) (δ n).1).1 ∩
        (if b then YPseq D₀ D₁ hD₀nomin hD₁nomin X Y n
          else D₀.master \ YPseq D₀ D₁ hD₀nomin hD₁nomin X Y n) := by
  obtain ⟨hBA, hAmem⟩ := xStep_spec D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
    hYmem hD₀mne hD₁mne δ n
  set A1 := (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
    (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) (δ n).1).1 with hA1def
  set B1 := (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
    (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) (δ n).1).2 with hB1def
  set YP := YPseq D₀ D₁ hD₀nomin hD₁nomin X Y n with hYPdef
  have hspec := splitChoice'_isSplitSpec D₀ hD₀nomin hBA hAmem (Y n)
  have hJeqTrue : (yStep D₀ hD₀nomin A1 B1 (Y n) true).1 = A1 ∩ YP :=
    yStep_fst_eq_inter_YPseq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem
      hD₀mne hD₁mne δ n
  by_cases hb : b = true
  · rw [hb, ite_eq_left rfl]; exact hJeqTrue
  · rw [Bool.not_eq_true] at hb; subst hb
    rw [ite_eq_right (by simp)]
    have hJeq : (yStep D₀ hD₀nomin A1 B1 (Y n) false).1 = A1 \ YP := by
      have hunion : (yStep D₀ hD₀nomin A1 B1 (Y n) true).1 ∪ (yStep D₀ hD₀nomin A1 B1 (Y n) false).1
          = A1 := by simp only [yStep, xyStep, Prod.swap]; exact hspec.2.2.2.2.1
      have hinter : (yStep D₀ hD₀nomin A1 B1 (Y n) true).1 ∩ (yStep D₀ hD₀nomin A1 B1 (Y n) false).1
          = ∅ := by simp only [yStep, xyStep, Prod.swap]; exact hspec.2.2.2.2.2
      ext x
      constructor
      · intro hxJ
        have hxA1 : x ∈ A1 := hunion ▸ Or.inr hxJ
        refine ⟨hxA1, fun hxYP => ?_⟩
        have hxI : x ∈ (yStep D₀ hD₀nomin A1 B1 (Y n) true).1 := hJeqTrue ▸ Set.mem_inter hxA1 hxYP
        exact absurd (Set.mem_inter hxI hxJ) (by rw [hinter]; simp)
      · rintro ⟨hxA1, hxnYP⟩
        rw [← hunion] at hxA1
        rcases hxA1 with hxI | hxJ
        · exact absurd (hJeqTrue ▸ hxI : x ∈ A1 ∩ YP).2 hxnYP
        · exact hxJ
    rw [hJeq]
    have hsub : A1 ⊆ D₀.master := (xStep_fst_subset D₁ hD₁nomin _ _ (X n) (δ n).1).trans
      (atomPair_fst_subset_master D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
        hYmem hD₀mne hD₁mne δ n)
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩; exact ⟨hx1, hsub hx1, hx2⟩
    · rintro ⟨hx1, -, hx2⟩; exact ⟨hx1, hx2⟩

end AtomPair

end DomainTheory.NeighbourhoodSystems

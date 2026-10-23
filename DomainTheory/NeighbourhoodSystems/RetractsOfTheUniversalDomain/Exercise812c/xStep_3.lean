module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.part_c_2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.xStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.atomPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.atomPair_2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.XPseq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.subset
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.IsEffectivelyGiven
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCode_disjoint_YseqCode_of_posTwin_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCode_succ_true
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.hcoreIdxYc
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.transfer_dir_idxYc
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtomDecidable.DAtom_eq_empty_iff

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
namespace xStep

open NeighborhoodSystem

section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

/-- **The "I-formula" for `XPseq`**: the `D₁`-piece chosen by the depth-`n` `X`-sub-step's "+"
branch (for *any* history `δ`) is exactly the intersection of `atomPair δ n`'s `D₁`-side with
`XPseq n`. Mirrors `Theorem88.lean`'s `split_fst_eq_inter_Yseq`, but proved directly against
`atomPair`'s own invariants (no `atomE`/`genAtom` involved — see the section docstring above). -/
theorem snd_eq_inter_XPseq (δ : ℕ → Bool × Bool) (n : ℕ) :
    (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
        (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) true).2 =
      (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 ∩ XPseq D₀ D₁ hD₀nomin hD₁nomin X Y n := by
  obtain ⟨hAB, -, hBmem⟩ := atomPair.invariant D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff
    hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne δ n
  set A := (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1 with hAdef
  set B := (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 with hBdef
  set I := (xStep D₁ hD₁nomin A B (X n) true).2 with hIdef
  apply Set.Subset.antisymm
  · have hIsubB : I ⊆ B := xStep.snd_subset hD₁nomin hAB hBmem (X n) true
    have hIsubX : I ⊆ XPseq D₀ D₁ hD₀nomin hD₁nomin X Y n := by
      have hcongr : atomPair D₀ D₁ hD₀nomin hD₁nomin X Y
          (extendTruePair (restrictFinPair δ n)) n =
          atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n :=
        atomPair.congr D₀ D₁ hD₀nomin hD₁nomin X Y
          (fun i hi => extendTruePair_restrictFinPair_agree δ n i hi)
      have hmem := subset.XPseq D₀ D₁ hD₀nomin hD₁nomin X Y (restrictFinPair δ n)
      rwa [hcongr] at hmem
    exact Set.subset_inter hIsubB hIsubX
  · rintro z ⟨hzB, hzX⟩
    obtain ⟨δ', hz'⟩ := Set.mem_iUnion.mp hzX
    by_cases hagree : ∀ i < n, extendTruePair δ' i = δ i
    · have hABeq : atomPair D₀ D₁ hD₀nomin hD₁nomin X Y (extendTruePair δ') n =
          atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n :=
        atomPair.congr D₀ D₁ hD₀nomin hD₁nomin X Y hagree
      rwa [hABeq] at hz'
    · push Not at hagree
      obtain ⟨j, hj, hjne⟩ := hagree
      have hdisjBB := (atomPair.disjoint D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin
        X Y hXmem hYmem hD₀mne hD₁mne (extendTruePair δ') δ n ⟨j, hj, hjne⟩).2
      obtain ⟨hAB', -, hBmem'⟩ := atomPair.invariant D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff
        hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne (extendTruePair δ') n
      have hzB' : z ∈ (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y (extendTruePair δ') n).2 :=
        xStep.snd_subset hD₁nomin hAB' hBmem' (X n) true hz'
      exact absurd (Set.mem_inter hzB' hzB) (by rw [hdisjBB]; simp)

end AtomPair

end xStep
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace xStep

open NeighborhoodSystem

section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

/-- **Two-branch closed form for the `X`-sub-step's `D₁`-side output** (Exercise 8.12(c)(vi)(5)(a)):
completes `xStep.snd_eq_inter_XPseq`'s `true`-only I-formula into a full `genAtom`-shaped recursive
step at *either* sign, mirroring `Theorem88.lean`'s `atomU_succ_eq` exactly — the `false` branch is
derived algebraically from the `true` branch plus `SplitSpec'`'s `I ∪ J = B`/`I ∩ J = ∅`, with no
new disjointness or invariant content. -/
theorem snd_succ_eq (δ : ℕ → Bool × Bool) (n : ℕ) (b : Bool) :
    (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
        (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) b).2 =
      (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 ∩
        (if b then XPseq D₀ D₁ hD₀nomin hD₁nomin X Y n
          else D₁.master \ XPseq D₀ D₁ hD₀nomin hD₁nomin X Y n) := by
  obtain ⟨hAB, -, hBmem⟩ := atomPair.invariant D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff
    hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne δ n
  set A := (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1 with hAdef
  set B := (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 with hBdef
  set XP := XPseq D₀ D₁ hD₀nomin hD₁nomin X Y n with hXPdef
  have hspec := splitChoice'_isSplitSpec D₁ hD₁nomin hAB hBmem (X n)
  have hIeq : (xStep D₁ hD₁nomin A B (X n) true).2 = B ∩ XP :=
    xStep.snd_eq_inter_XPseq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem
      hD₀mne hD₁mne δ n
  by_cases hb : b = true
  · rw [hb, ite_eq_left rfl]; exact hIeq
  · rw [Bool.not_eq_true] at hb; subst hb
    rw [ite_eq_right (by simp)]
    have hJeq : (xStep D₁ hD₁nomin A B (X n) false).2 = B \ XP := by
      have hunion : (xStep D₁ hD₁nomin A B (X n) true).2 ∪ (xStep D₁ hD₁nomin A B (X n) false).2
          = B := by simp only [xStep, xyStep]; exact hspec.2.2.2.2.1
      have hinter : (xStep D₁ hD₁nomin A B (X n) true).2 ∩ (xStep D₁ hD₁nomin A B (X n) false).2
          = ∅ := by simp only [xStep, xyStep]; exact hspec.2.2.2.2.2
      ext x
      constructor
      · intro hxJ
        have hxB : x ∈ B := hunion ▸ Or.inr hxJ
        refine ⟨hxB, fun hxXP => ?_⟩
        have hxI : x ∈ (xStep D₁ hD₁nomin A B (X n) true).2 := hIeq ▸ Set.mem_inter hxB hxXP
        exact absurd (Set.mem_inter hxI hxJ) (by rw [hinter]; simp)
      · rintro ⟨hxB, hxnXP⟩
        rw [← hunion] at hxB
        rcases hxB with hxI | hxJ
        · exact absurd (hIeq ▸ hxI : x ∈ B ∩ XP).2 hxnXP
        · exact hxJ
    rw [hJeq]
    have hsub := atomPair.snd_subset_master D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin
      X Y hXmem hYmem hD₀mne hD₁mne δ n
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩; exact ⟨hx1, hsub hx1, hx2⟩
    · rintro ⟨hx1, -, hx2⟩; exact ⟨hx1, hx2⟩

end AtomPair

end xStep
end DomainTheory.NeighbourhoodSystems

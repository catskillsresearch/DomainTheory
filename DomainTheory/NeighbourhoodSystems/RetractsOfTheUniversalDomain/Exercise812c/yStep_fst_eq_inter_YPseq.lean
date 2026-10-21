/-ai
The first output of the true-bit Y-step, applied after the X-step at the first sign bit of the history, equals that post-X first value intersected with YPseq at n.

The bit-general specification of the X-step gives matching emptiness and the empty-or-neighbourhood alternative for the post-X pair. For one inclusion, the output lies in the post-X first value, and it lies in YPseq because the padding of the restricted history agrees with the history below n, so the atoms agree and the corresponding summand contains the output. For the other inclusion, an element of the intersection belongs to some summand, for some prefix and some bit. If the padded prefix agrees with the history below n and the bit equals the first sign bit, the atoms agree and the element is the output. If the histories agree below n but the bits differ, the two first outputs of the X-step are disjoint, while the element lies in both because the Y-output sits inside its X-step first output. If the histories disagree below n, the two first components of atomPair are disjoint, while the element lies in both: the foreign Y-output sits inside the foreign X-step output and hence inside the foreign atom, and the home element sits inside the home atom.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.extendTruePair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.restrictFinPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.extendTruePair_restrictFinPair_agree
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.xStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.yStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.xStep_fst_subset
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.yStep_fst_subset
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.xStep_disjoint_of_ne
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.atomPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.atomPair_invariant
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.atomPair_congr
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.atomPair_disjoint
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.YPseq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.subset_YPseq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.xStep_spec_bit
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

section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

/-- **The "I-formula" for `YPseq`** (8.12(c)(vi)(4)(d)): the `D₀`-piece chosen by the `Y`-sub-step's
"+" branch (applied to the post-`X`-sub-step values at *any* history `δ`'s own bit `(δ n).1`) is
exactly the intersection of that post-`X`-sub-step `D₀`-value with `YPseq n`. Mirrors
`xStep_snd_eq_inter_XPseq`, but needs `xStep_spec_bit`'s bridge (unlike `XPseq`'s proof) to handle
the `⊇` direction's "history agrees below `n` but the union's bit differs from `(δ n).1`" case. -/
theorem yStep_fst_eq_inter_YPseq (δ : ℕ → Bool × Bool) (n : ℕ) :
    (yStep D₀ hD₀nomin
        (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
          (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) (δ n).1).1
        (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
          (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) (δ n).1).2
        (Y n) true).1 =
      (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
          (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) (δ n).1).1 ∩
        YPseq D₀ D₁ hD₀nomin hD₁nomin X Y n := by
  obtain ⟨hBA, hAmem⟩ := xStep_spec_bit D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin
    X Y hXmem hYmem hD₀mne hD₁mne δ n (δ n).1
  set A1 := (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
    (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) (δ n).1).1 with hA1def
  set B1 := (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
    (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) (δ n).1).2 with hB1def
  set J := (yStep D₀ hD₀nomin A1 B1 (Y n) true).1 with hJdef
  apply Set.Subset.antisymm
  · have hJsubA1 : J ⊆ A1 := yStep_fst_subset hD₀nomin hBA hAmem (Y n) true
    have hJsubY : J ⊆ YPseq D₀ D₁ hD₀nomin hD₁nomin X Y n := by
      have hcongr : atomPair D₀ D₁ hD₀nomin hD₁nomin X Y
          (extendTruePair (restrictFinPair δ n)) n =
          atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n :=
        atomPair_congr D₀ D₁ hD₀nomin hD₁nomin X Y
          (fun i hi => extendTruePair_restrictFinPair_agree δ n i hi)
      have hmem := subset_YPseq D₀ D₁ hD₀nomin hD₁nomin X Y (restrictFinPair δ n) (δ n).1
      rwa [hcongr] at hmem
    exact Set.subset_inter hJsubA1 hJsubY
  · rintro z ⟨hzA1, hzY⟩
    obtain ⟨δ', hz'⟩ := Set.mem_iUnion.mp hzY
    obtain ⟨bx, hz''⟩ := Set.mem_iUnion.mp hz'
    by_cases hagree : ∀ i < n, extendTruePair δ' i = δ i
    · have hABeq : atomPair D₀ D₁ hD₀nomin hD₁nomin X Y (extendTruePair δ') n =
          atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n :=
        atomPair_congr D₀ D₁ hD₀nomin hD₁nomin X Y hagree
      by_cases hbxeq : bx = (δ n).1
      · rw [hABeq, hbxeq] at hz''
        exact hz''
      · obtain ⟨hAB, -, hBmem⟩ := atomPair_invariant D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff
          hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne δ n
        have hxdisj := xStep_disjoint_of_ne hD₁nomin hAB hBmem (X n) hbxeq
        rw [hABeq] at hz''
        have hzA1' : z ∈ (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
            (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) bx).1 := by
          obtain ⟨hBA', hAmem'⟩ := xStep_spec_bit D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff
            hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne δ n bx
          exact yStep_fst_subset hD₀nomin hBA' hAmem' (Y n) true hz''
        exact absurd (Set.mem_inter hzA1' hzA1) (by rw [hxdisj.1]; simp)
    · push Not at hagree
      obtain ⟨j, hj, hjne⟩ := hagree
      have hdisjAA := (atomPair_disjoint D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin
        X Y hXmem hYmem hD₀mne hD₁mne (extendTruePair δ') δ n ⟨j, hj, hjne⟩).1
      have hzA1' : z ∈ (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y (extendTruePair δ') n).1 := by
        obtain ⟨hBA', hAmem'⟩ := xStep_spec_bit D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff
          hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne (extendTruePair δ') n bx
        have hJ'subA1' := yStep_fst_subset hD₀nomin hBA' hAmem' (Y n) true hz''
        exact xStep_fst_subset D₁ hD₁nomin _ _ (X n) bx hJ'subA1'
      have hzAfull : z ∈ (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1 :=
        xStep_fst_subset D₁ hD₁nomin _ _ (X n) (δ n).1 hzA1
      exact absurd (Set.mem_inter hzA1' hzAfull) (by rw [hdisjAA]; simp)

end AtomPair

end DomainTheory.NeighbourhoodSystems

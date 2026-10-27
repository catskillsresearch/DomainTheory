module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.V
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem_8_8
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.VComputablePresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise_7_18
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem_7_5
public import Mathlib.Data.Nat.Bitwise
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise_3_26
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.atomPair812c
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.XPseq812c
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.splitSpec812c
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.combinedXY812c

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

/-- The interleaved family testing `D₁`'s side: at even positions, `XPseq`'s recovered `D₁`-side
pieces; at odd positions, `Y`'s own enumeration. -/
noncomputable def combinedY (n : ℕ) : Set β :=
  if n % 2 = 0 then XPseq D₀ D₁ hD₀nomin hD₁nomin X Y (n / 2) else Y (n / 2)

end AtomPair
end

namespace combinedY
open NeighborhoodSystem

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

omit hD₀pos hD₀diff hD₁pos hD₁diff hXmem hYmem hD₀mne hD₁mne in

theorem even (k : ℕ) :
    combinedY D₀ D₁ hD₀nomin hD₁nomin X Y (2 * k) = XPseq D₀ D₁ hD₀nomin hD₁nomin X Y k := by
  unfold combinedY
  rw [ite_eq_left (by omega : (2 * k) % 2 = 0), show (2 * k) / 2 = k from by omega]

omit hD₀pos hD₀diff hD₁pos hD₁diff hXmem hYmem hD₀mne hD₁mne in
theorem odd (k : ℕ) : combinedY D₀ D₁ hD₀nomin hD₁nomin X Y (2 * k + 1) = Y k := by
  unfold combinedY
  rw [ite_eq_right (by omega : ¬ (2 * k + 1) % 2 = 0), show (2 * k + 1) / 2 = k from by omega]

end AtomPair
end

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

/-- `combinedY i` is always `⊆ D₁.master`, symmetric to `combinedX.subset_master`: at even
positions it is `XPseq (i/2)`, already known `⊆ D₁.master`; at odd positions it is `Y (i/2)`, a
`D₁.mem` set (via `D₁.sub_master`). -/
theorem subset_master (i : ℕ) :
    combinedY D₀ D₁ hD₀nomin hD₁nomin X Y i ⊆ D₁.master := by
  rcases (by omega : i % 2 = 0 ∨ i % 2 = 1) with hi | hi
  · rw [show i = 2 * (i / 2) from by omega, combinedY.even]
    exact XPseq.subset_master D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem
      hD₀mne hD₁mne (i / 2)
  · rw [show i = 2 * (i / 2) + 1 from by omega, combinedY.odd]
    exact D₁.sub_master (hYmem (i / 2))

end AtomPair
end

end combinedY
namespace xStep
open NeighborhoodSystem

section
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
end

end xStep
namespace genAtom
open NeighborhoodSystem

/-- **`genAtom`'s own recursive equation, as a rewritable lemma** (mirrors `Theorem88.lean`'s
`atomU_succ`; `genAtom`'s `def` is a direct structural match on its `Nat` argument, so this holds by
`rfl`, but stating it separately lets `rw` fire on `Nat`-literal successor forms like `2 * n + 1 + 1`
without needing to unfold `genAtom` itself). -/
theorem succ' {γ : Type*} (Z : ℕ → Set γ) (M : Set γ) (δ : ℕ → Bool) (n : ℕ) :
    genAtom Z M δ (n + 1) = genAtom Z M δ n ∩ (if δ n then Z n else M \ Z n) := rfl

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne


/-- **The odd-depth half-step identity for `combinedX`**: given `atomPair δ n`'s `α`-side agrees
with `genAtom combinedX` at the even depth `2 * n`, it also agrees at the odd depth `2 * n + 1` with
the `Y`-sub-step's own (choice-split) `α`-side output — via (vi)(5)(a)'s closed form
`yStep.fst_succ_eq`, run at `combinedδ`/`combinedY`'s odd value `(δ n).2`. -/
theorem combinedX_succ_eq (δ : ℕ → Bool × Bool) (n : ℕ)
    (hn : (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1 =
      genAtom (combinedX D₀ D₁ hD₀nomin hD₁nomin X Y) D₀.master (combinedδ δ) (2 * n)) :
    genAtom (combinedX D₀ D₁ hD₀nomin hD₁nomin X Y) D₀.master (combinedδ δ) (2 * n + 1) =
      (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
        (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) (δ n).1).1 := by
  rw [genAtom.succ', ← hn, combinedδ_even, combinedX.even]
  have hAsub : (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1 ⊆ D₀.master :=
    atomPair.fst_subset_master D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
      hYmem hD₀mne hD₁mne δ n
  simp only [xStep, xyStep]
  rcases Bool.eq_false_or_eq_true (δ n).1 with hb | hb
  · simp only [hb, ite_true]
  · simp only [hb, Bool.false_eq_true, ite_false]
    exact inter.diff_eq_diff_of_subset hAsub


/-- **The odd-depth half-step identity for `combinedY`**: given `atomPair δ n`'s `β`-side agrees
with `genAtom combinedY` at the even depth `2 * n`, it also agrees at the odd depth `2 * n + 1` with
the `X`-sub-step's own (choice-split) `β`-side output — via (vi)(5)(a)'s closed form
`xStep.snd_succ_eq`, run at `combinedδ`/`combinedX`'s even value `(δ n).1`. -/
theorem combinedY_succ_eq (δ : ℕ → Bool × Bool) (n : ℕ)
    (hn : (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 =
      genAtom (combinedY D₀ D₁ hD₀nomin hD₁nomin X Y) D₁.master (combinedδ δ) (2 * n)) :
    genAtom (combinedY D₀ D₁ hD₀nomin hD₁nomin X Y) D₁.master (combinedδ δ) (2 * n + 1) =
      (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
        (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) (δ n).1).2 := by
  rw [genAtom.succ', ← hn, combinedδ_even, combinedY.even]
  exact (xStep.snd_succ_eq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem
    hD₀mne hD₁mne δ n (δ n).1).symm
end AtomPair
end

end genAtom
namespace yStep
open NeighborhoodSystem

section
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
`xStep.snd_eq_inter_XPseq`, but needs `xStep.spec_bit`'s bridge (unlike `XPseq`'s proof) to handle
the `⊇` direction's "history agrees below `n` but the union's bit differs from `(δ n).1`" case. -/
theorem fst_eq_inter_YPseq (δ : ℕ → Bool × Bool) (n : ℕ) :
    (yStep D₀ hD₀nomin
        (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
          (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) (δ n).1).1
        (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
          (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) (δ n).1).2
        (Y n) true).1 =
      (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
          (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) (δ n).1).1 ∩
        YPseq D₀ D₁ hD₀nomin hD₁nomin X Y n := by
  obtain ⟨hBA, hAmem⟩ := xStep.spec_bit D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin
    X Y hXmem hYmem hD₀mne hD₁mne δ n (δ n).1
  set A1 := (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
    (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) (δ n).1).1 with hA1def
  set B1 := (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
    (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) (δ n).1).2 with hB1def
  set J := (yStep D₀ hD₀nomin A1 B1 (Y n) true).1 with hJdef
  apply Set.Subset.antisymm
  · have hJsubA1 : J ⊆ A1 := yStep.fst_subset hD₀nomin hBA hAmem (Y n) true
    have hJsubY : J ⊆ YPseq D₀ D₁ hD₀nomin hD₁nomin X Y n := by
      have hcongr : atomPair D₀ D₁ hD₀nomin hD₁nomin X Y
          (extendTruePair (restrictFinPair δ n)) n =
          atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n :=
        atomPair.congr D₀ D₁ hD₀nomin hD₁nomin X Y
          (fun i hi => extendTruePair_restrictFinPair_agree δ n i hi)
      have hmem := subset.YPseq D₀ D₁ hD₀nomin hD₁nomin X Y (restrictFinPair δ n) (δ n).1
      rwa [hcongr] at hmem
    exact Set.subset_inter hJsubA1 hJsubY
  · rintro z ⟨hzA1, hzY⟩
    obtain ⟨δ', hz'⟩ := Set.mem_iUnion.mp hzY
    obtain ⟨bx, hz''⟩ := Set.mem_iUnion.mp hz'
    by_cases hagree : ∀ i < n, extendTruePair δ' i = δ i
    · have hABeq : atomPair D₀ D₁ hD₀nomin hD₁nomin X Y (extendTruePair δ') n =
          atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n :=
        atomPair.congr D₀ D₁ hD₀nomin hD₁nomin X Y hagree
      by_cases hbxeq : bx = (δ n).1
      · rw [hABeq, hbxeq] at hz''
        exact hz''
      · obtain ⟨hAB, -, hBmem⟩ := atomPair.invariant D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff
          hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne δ n
        have hxdisj := xStep.disjoint_of_ne hD₁nomin hAB hBmem (X n) hbxeq
        rw [hABeq] at hz''
        have hzA1' : z ∈ (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
            (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) bx).1 := by
          obtain ⟨hBA', hAmem'⟩ := xStep.spec_bit D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff
            hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne δ n bx
          exact yStep.fst_subset hD₀nomin hBA' hAmem' (Y n) true hz''
        exact absurd (Set.mem_inter hzA1' hzA1) (by rw [hxdisj.1]; simp)
    · push Not at hagree
      obtain ⟨j, hj, hjne⟩ := hagree
      have hdisjAA := (atomPair.disjoint D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin
        X Y hXmem hYmem hD₀mne hD₁mne (extendTruePair δ') δ n ⟨j, hj, hjne⟩).1
      have hzA1' : z ∈ (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y (extendTruePair δ') n).1 := by
        obtain ⟨hBA', hAmem'⟩ := xStep.spec_bit D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff
          hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne (extendTruePair δ') n bx
        have hJ'subA1' := yStep.fst_subset hD₀nomin hBA' hAmem' (Y n) true hz''
        exact xStep.fst_subset D₁ hD₁nomin _ _ (X n) bx hJ'subA1'
      have hzAfull : z ∈ (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1 :=
        xStep.fst_subset D₁ hD₁nomin _ _ (X n) (δ n).1 hzA1
      exact absurd (Set.mem_inter hzA1' hzAfull) (by rw [hdisjAA]; simp)


/-- **Two-branch closed form for the `Y`-sub-step's `D₀`-side output** (Exercise 8.12(c)(vi)(5)(a)):
completes `yStep.fst_eq_inter_YPseq`'s `true`-only I-formula into a full `genAtom`-shaped recursive
step at *either* sign of the `Y`-sub-step itself (the `X`-sub-step's own bit stays fixed at `(δ
n).1`, exactly as in `yStep.fst_eq_inter_YPseq` — no `xStep.spec_bit`-style further generalization
is needed here, since 8.12(c)(vi)(5)(b)'s combined-family recursion only ever calls this at `δ`'s
own bit). Mirrors `xStep.snd_succ_eq` above (equivalently `Theorem88.lean`'s `atomU_succ_eq`), with
the `false` branch derived algebraically from the `true` branch plus `SplitSpec'`'s `I ∪ J = B`/
`I ∩ J = ∅`. -/
theorem fst_succ_eq (δ : ℕ → Bool × Bool) (n : ℕ) (b : Bool) :
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
  obtain ⟨hBA, hAmem⟩ := xStep.spec D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
    hYmem hD₀mne hD₁mne δ n
  set A1 := (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
    (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) (δ n).1).1 with hA1def
  set B1 := (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
    (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) (δ n).1).2 with hB1def
  set YP := YPseq D₀ D₁ hD₀nomin hD₁nomin X Y n with hYPdef
  have hspec := splitChoice'_isSplitSpec D₀ hD₀nomin hBA hAmem (Y n)
  have hJeqTrue : (yStep D₀ hD₀nomin A1 B1 (Y n) true).1 = A1 ∩ YP :=
    yStep.fst_eq_inter_YPseq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem
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
    have hsub : A1 ⊆ D₀.master := (xStep.fst_subset D₁ hD₁nomin _ _ (X n) (δ n).1).trans
      (atomPair.fst_subset_master D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
        hYmem hD₀mne hD₁mne δ n)
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩; exact ⟨hx1, hsub hx1, hx2⟩
    · rintro ⟨hx1, -, hx2⟩; exact ⟨hx1, hx2⟩
end AtomPair
end

end yStep
namespace atomPair
open NeighborhoodSystem

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne


/-- **Headline closed form, `β`-side** (Exercise 8.12(c)(vi)(5)(b)), symmetric to
`atomPair.fst_eq_genAtom`: `atomPair δ n`'s `β`-side coincides with `genAtom` over the interleaved
family `combinedY` at depth `2 * n`, via `genAtom.combinedY_succ_eq` ((vi)(5)(a)'s `X`-sub-step
closed form `xStep.snd_succ_eq`) then the `Y`-sub-step's direct `β`-side output (elementary, no
closed form needed — it is literally `if (δ n).2 then B1 ∩ Y n else B1 \ Y n` by `yStep`'s own
definition). -/
theorem snd_eq_genAtom (δ : ℕ → Bool × Bool) (n : ℕ) :
    (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 =
      genAtom (combinedY D₀ D₁ hD₀nomin hD₁nomin X Y) D₁.master (combinedδ δ) (2 * n) := by
  induction n with
  | zero => rfl
  | succ n hIH =>
      have hodd := genAtom.combinedY_succ_eq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin
        X Y hXmem hYmem hD₀mne hD₁mne δ n hIH
      have h2 : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
      rw [atomPair.succ_eq, h2, genAtom.succ', combinedδ_odd, combinedY.odd, hodd]
      obtain ⟨hAB, -, hBmem⟩ := atomPair.invariant D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff
        hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne δ n
      have hB1sub := (xStep.snd_subset hD₁nomin hAB hBmem (X n) (δ n).1).trans
        (atomPair.snd_subset_master D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
          hYmem hD₀mne hD₁mne δ n)
      simp only [yStep, xyStep, Prod.swap]
      rcases Bool.eq_false_or_eq_true (δ n).2 with hb | hb
      · simp only [hb, ite_true]
      · simp only [hb, Bool.false_eq_true, ite_false]
        exact (inter.diff_eq_diff_of_subset hB1sub).symm


/-- **Headline closed form, `α`-side** (Exercise 8.12(c)(vi)(5)(b)): `atomPair δ n`'s `α`-side
coincides with `genAtom` over the interleaved family `combinedX` at the doubled depth `2 * n`.
Proved by induction on `n`, each step performing the two half-step rewrites
`genAtom.combinedX_succ_eq` (`X`-sub-step half, elementary) then `yStep.fst_succ_eq` ((vi)(5)(a)'s
`Y`-sub-step closed form) — mirrors `Theorem88.lean`'s one-line `atomU_eq_genAtom`, just with each
level's step split into the two named half-steps. -/
theorem fst_eq_genAtom (δ : ℕ → Bool × Bool) (n : ℕ) :
    (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1 =
      genAtom (combinedX D₀ D₁ hD₀nomin hD₁nomin X Y) D₀.master (combinedδ δ) (2 * n) := by
  induction n with
  | zero => rfl
  | succ n hIH =>
      have hodd := genAtom.combinedX_succ_eq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin
        X Y hXmem hYmem hD₀mne hD₁mne δ n hIH
      have hstep := yStep.fst_succ_eq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y
        hXmem hYmem hD₀mne hD₁mne δ n (δ n).2
      have h2 : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
      rw [atomPair.succ_eq, hstep, h2, genAtom.succ', combinedδ_odd, combinedX.odd, hodd]
end AtomPair
end

end atomPair


end DomainTheory.NeighbourhoodSystems

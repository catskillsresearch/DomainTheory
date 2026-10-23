module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.other_2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.part_c_2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.union
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xStepG
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.yStepG
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateRemC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.other
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.deltaPair

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section AtomPairGen

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hySplit : SplitSpec' D₀ splitY)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hxSplit : SplitSpec' D₁ splitX)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

/-- **Generalized `atomPair`**, taking the split functions directly instead of deriving them from
`NoMinimal` witnesses. -/
noncomputable def atomPairG (δ : ℕ → Bool × Bool) : ℕ → Set α × Set β
  | 0 => (D₀.master, D₁.master)
  | (n + 1) =>
      let A := (atomPairG δ n).1
      let B := (atomPairG δ n).2
      let IJ1 := splitX A B (X n)
      let A1 := if (δ n).1 then A ∩ X n else A \ X n
      let B1 := if (δ n).1 then IJ1.1 else IJ1.2
      let IJ2 := splitY B1 A1 (Y n)
      let B2 := if (δ n).2 then B1 ∩ Y n else B1 \ Y n
      let A2 := if (δ n).2 then IJ2.1 else IJ2.2
      (A2, B2)

end AtomPairGen

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace atomPairG

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section AtomPairGen

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hySplit : SplitSpec' D₀ splitY)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hxSplit : SplitSpec' D₁ splitX)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hySplit hD₁pos hD₁diff hxSplit hXmem hYmem hD₀mne hD₁mne

omit hD₀pos hD₀diff hySplit hD₁pos hD₁diff hxSplit hXmem hYmem hD₀mne hD₁mne in
/-- Extending/changing `δ` at or beyond position `n` does not change `atomPairG δ n`. -/
theorem congr {δ δ' : ℕ → Bool × Bool} {n : ℕ} (h : ∀ i < n, δ i = δ' i) :
    atomPairG D₀ D₁ splitY splitX X Y δ n = atomPairG D₀ D₁ splitY splitX X Y δ' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hprev : atomPairG D₀ D₁ splitY splitX X Y δ n =
        atomPairG D₀ D₁ splitY splitX X Y δ' n := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have hn : δ n = δ' n := h n (Nat.lt_succ_self n)
    show
      (let A := (atomPairG D₀ D₁ splitY splitX X Y δ n).1
       let B := (atomPairG D₀ D₁ splitY splitX X Y δ n).2
       let IJ1 := splitX A B (X n)
       let A1 := if (δ n).1 then A ∩ X n else A \ X n
       let B1 := if (δ n).1 then IJ1.1 else IJ1.2
       let IJ2 := splitY B1 A1 (Y n)
       let B2 := if (δ n).2 then B1 ∩ Y n else B1 \ Y n
       let A2 := if (δ n).2 then IJ2.1 else IJ2.2
       (A2, B2)) =
        (let A := (atomPairG D₀ D₁ splitY splitX X Y δ' n).1
         let B := (atomPairG D₀ D₁ splitY splitX X Y δ' n).2
         let IJ1 := splitX A B (X n)
         let A1 := if (δ' n).1 then A ∩ X n else A \ X n
         let B1 := if (δ' n).1 then IJ1.1 else IJ1.2
         let IJ2 := splitY B1 A1 (Y n)
         let B2 := if (δ' n).2 then B1 ∩ Y n else B1 \ Y n
         let A2 := if (δ' n).2 then IJ2.1 else IJ2.2
         (A2, B2))
    rw [hprev, hn]

end AtomPairGen

end atomPairG
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace atomPairG

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section AtomPairGen

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hySplit : SplitSpec' D₀ splitY)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hxSplit : SplitSpec' D₁ splitX)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hySplit hD₁pos hD₁diff hxSplit hXmem hYmem hD₀mne hD₁mne

/-- **The core invariant, generalized.** Direct transcription of `atomPair.invariant`. -/
theorem invariant (δ : ℕ → Bool × Bool) :
    ∀ n, ((atomPairG D₀ D₁ splitY splitX X Y δ n).1 = ∅ ↔
        (atomPairG D₀ D₁ splitY splitX X Y δ n).2 = ∅) ∧
      ((atomPairG D₀ D₁ splitY splitX X Y δ n).1 = ∅ ∨
        D₀.mem (atomPairG D₀ D₁ splitY splitX X Y δ n).1) ∧
      ((atomPairG D₀ D₁ splitY splitX X Y δ n).2 = ∅ ∨
        D₁.mem (atomPairG D₀ D₁ splitY splitX X Y δ n).2) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, Or.inr D₀.master_mem, Or.inr D₁.master_mem⟩
    show (D₀.master = ∅ ↔ D₁.master = ∅)
    exact ⟨fun h => absurd h hD₀mne.ne_empty, fun h => absurd h hD₁mne.ne_empty⟩
  | succ n ih =>
    obtain ⟨ihAB, ihA, ihB⟩ := ih
    set A := (atomPairG D₀ D₁ splitY splitX X Y δ n).1 with hAdef
    set B := (atomPairG D₀ D₁ splitY splitX X Y δ n).2 with hBdef
    have hspec1 := hxSplit ihAB ihB (X n)
    set I1 := (splitX A B (X n)).1 with hI1def
    set J1 := (splitX A B (X n)).2 with hJ1def
    set A1 := (if (δ n).1 then A ∩ X n else A \ X n) with hA1def
    set B1 := (if (δ n).1 then I1 else J1) with hB1def
    have hA1B1 : A1 = ∅ ↔ B1 = ∅ := by
      by_cases hδ1 : (δ n).1 = true
      · simp only [hA1def, hB1def, hδ1, ite_true]; exact hspec1.2.2.1
      · simp only [hA1def, hB1def, hδ1]; exact hspec1.2.2.2.1
    have hA1mem : A1 = ∅ ∨ D₀.mem A1 := by
      by_cases hδ1 : (δ n).1 = true
      · simp only [hA1def, hδ1, ite_true]; exact inter.mem_or_empty hD₀pos ihA (hXmem n)
      · simp only [hA1def, hδ1]; exact diff.mem_or_empty hD₀diff ihA (hXmem n)
    have hB1mem : B1 = ∅ ∨ D₁.mem B1 := by
      by_cases hδ1 : (δ n).1 = true
      · simp only [hB1def, hδ1, ite_true]; exact hspec1.1
      · simp only [hB1def, hδ1]; exact hspec1.2.1
    have hspec2 := hySplit hA1B1.symm hA1mem (Y n)
    set I2 := (splitY B1 A1 (Y n)).1 with hI2def
    set J2 := (splitY B1 A1 (Y n)).2 with hJ2def
    set B2 := (if (δ n).2 then B1 ∩ Y n else B1 \ Y n) with hB2def
    set A2 := (if (δ n).2 then I2 else J2) with hA2def
    have hB2A2 : B2 = ∅ ↔ A2 = ∅ := by
      by_cases hδ2 : (δ n).2 = true
      · simp only [hB2def, hA2def, hδ2, ite_true]; exact hspec2.2.2.1
      · simp only [hB2def, hA2def, hδ2]; exact hspec2.2.2.2.1
    have hB2mem : B2 = ∅ ∨ D₁.mem B2 := by
      by_cases hδ2 : (δ n).2 = true
      · simp only [hB2def, hδ2, ite_true]; exact inter.mem_or_empty hD₁pos hB1mem (hYmem n)
      · simp only [hB2def, hδ2]; exact diff.mem_or_empty hD₁diff hB1mem (hYmem n)
    have hA2mem : A2 = ∅ ∨ D₀.mem A2 := by
      by_cases hδ2 : (δ n).2 = true
      · simp only [hA2def, hδ2, ite_true]; exact hspec2.1
      · simp only [hA2def, hδ2]; exact hspec2.2.1
    show (A2 = ∅ ↔ B2 = ∅) ∧ (A2 = ∅ ∨ D₀.mem A2) ∧ (B2 = ∅ ∨ D₁.mem B2)
    exact ⟨hB2A2.symm, hA2mem, hB2mem⟩

end AtomPairGen

end atomPairG
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace atomPairG

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section AtomPairGen

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hySplit : SplitSpec' D₀ splitY)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hxSplit : SplitSpec' D₁ splitX)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

theorem succ_eq (δ : ℕ → Bool × Bool) (n : ℕ) :
    atomPairG D₀ D₁ splitY splitX X Y δ (n + 1) =
      yStepG splitY
        (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) (δ n).1).1
        (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) (δ n).1).2
        (Y n) (δ n).2 := rfl

end AtomPairGen

end atomPairG
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace atomPairG

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section AtomPairGen

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hySplit : SplitSpec' D₀ splitY)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hxSplit : SplitSpec' D₁ splitX)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hySplit hD₁pos hD₁diff hxSplit hXmem hYmem hD₀mne hD₁mne

/-- **8.12(d)(4)(c)(i): the one-step 4-way classical reunion.** Ranging over all four
`(b1, b2) : Bool × Bool` sign choices at depth `n`, the resulting depth-`(n+1)` `D₀`-pieces
reunion to *exactly* the depth-`n` parent's `D₀`-piece — the algebraic core of the covering
argument closing `XPseqCode`'s deferred unconditional-"found" gap (`(d)(4)(c)`'s nested sub-goals).
Two facts chained: `xStepG.fst_union` at the `b1`-level (no hypotheses needed) and `yStepG.fst_union`
at the `b2`-level (needs `xStepG`'s output to satisfy `SplitSpec'`'s preconditions, supplied by the
same case analysis `xStepG.spec` already does, inlined here since `xStepG.spec` itself is hardcoded
to `(δ n).1` rather than a free `b1`). -/
theorem fst_union_step (δ : ℕ → Bool × Bool) (n : ℕ) :
    ((yStepG splitY (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) true).1
        (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) true).2 (Y n) true).1 ∪
      (yStepG splitY (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) true).1
        (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) true).2 (Y n) false).1) ∪
    ((yStepG splitY (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) false).1
        (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) false).2 (Y n) true).1 ∪
      (yStepG splitY (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) false).1
        (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) false).2 (Y n) false).1) =
      (atomPairG D₀ D₁ splitY splitX X Y δ n).1 := by
  obtain ⟨ihAB, ihA, ihB⟩ := atomPairG.invariant D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
    splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne δ n
  set A := (atomPairG D₀ D₁ splitY splitX X Y δ n).1 with hAdef
  set B := (atomPairG D₀ D₁ splitY splitX X Y δ n).2 with hBdef
  have hspec1 := hxSplit ihAB ihB (X n)
  have hBAtrue : (xStepG splitX A B (X n) true).2 = ∅ ↔ (xStepG splitX A B (X n) true).1 = ∅ := by
    simp only [xStepG, xyStep, ite_true]; exact hspec1.2.2.1.symm
  have hAmemtrue : (xStepG splitX A B (X n) true).1 = ∅ ∨ D₀.mem (xStepG splitX A B (X n) true).1 := by
    simp only [xStepG, xyStep, ite_true]; exact inter.mem_or_empty hD₀pos ihA (hXmem n)
  have hBAfalse : (xStepG splitX A B (X n) false).2 = ∅ ↔ (xStepG splitX A B (X n) false).1 = ∅ := by
    simp only [xStepG, xyStep]; exact hspec1.2.2.2.1.symm
  have hAmemfalse : (xStepG splitX A B (X n) false).1 = ∅ ∨ D₀.mem (xStepG splitX A B (X n) false).1 := by
    simp only [xStepG, xyStep]; exact diff.mem_or_empty hD₀diff ihA (hXmem n)
  rw [yStepG.fst_union hySplit hBAtrue hAmemtrue (Y n),
    yStepG.fst_union hySplit hBAfalse hAmemfalse (Y n)]
  exact xStepG.fst_union splitX A B (X n)

end AtomPairGen

end atomPairG
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace atomPairG

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section AtomPairGen

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hySplit : SplitSpec' D₀ splitY)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hxSplit : SplitSpec' D₁ splitX)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hySplit hD₁pos hD₁diff hxSplit hXmem hYmem hD₀mne hD₁mne

/-- **8.12(d)(4)(c)(ii): classical covering induction.** The classical `atomPairG` pieces at depth
`n`, ranged over all sign-histories `δ' : Fin n → Bool × Bool` (padded to `ℕ → Bool × Bool` via
`extendTruePair`), cover `D₀.master`. Induction on `n` chaining `atomPairG.fst_union_step` at every
step; base case `n = 0` is trivial (`atomPairG _ 0 = (D₀.master, D₁.master)`, one piece covering
itself). The successor step extends a covering history `δ'₀ : Fin n → Bool × Bool` for `z` by one
more `(b1, b2) : Bool × Bool` bit via the usual `Function.update`-based device (`extendTruePair
δ'₀` updated at `n`, then `restrictFinPair`'d back down to `Fin (n + 1) → Bool × Bool`; mirrors
`Exercise812c.lean`'s `xStep.spec_bit`/`yStep.fst_eq_inter_YPseq` proofs), picking whichever of the
four `atomPairG.fst_union_step` branches `z` actually landed in. -/
theorem master_covered (n : ℕ) :
    ∀ z ∈ D₀.master, ∃ δ' : Fin n → Bool × Bool,
      z ∈ (atomPairG D₀ D₁ splitY splitX X Y (extendTruePair δ') n).1 := by
  induction n with
  | zero => exact fun z hz => ⟨Fin.elim0, hz⟩
  | succ n ih =>
    intro z hz
    obtain ⟨δ'₀, hδ'₀⟩ := ih z hz
    have hcover := atomPairG.fst_union_step D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
      splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne (extendTruePair δ'₀) n
    set A := (atomPairG D₀ D₁ splitY splitX X Y (extendTruePair δ'₀) n).1 with hAdef
    set B := (atomPairG D₀ D₁ splitY splitX X Y (extendTruePair δ'₀) n).2 with hBdef
    have step : ∀ b1 b2 : Bool,
        z ∈ (yStepG splitY (xStepG splitX A B (X n) b1).1 (xStepG splitX A B (X n) b1).2
          (Y n) b2).1 →
        ∃ δ' : Fin (n + 1) → Bool × Bool,
          z ∈ (atomPairG D₀ D₁ splitY splitX X Y (extendTruePair δ') (n + 1)).1 := by
      intro b1 b2 hz'
      set δ'' := Function.update (extendTruePair δ'₀) n (b1, b2) with hδ''def
      refine ⟨restrictFinPair δ'' (n + 1), ?_⟩
      have hagree : ∀ i < n + 1, extendTruePair (restrictFinPair δ'' (n + 1)) i = δ'' i :=
        fun i hi => extendTruePair_restrictFinPair_agree δ'' (n + 1) i hi
      rw [atomPairG.congr D₀ D₁ splitY splitX X Y hagree, atomPairG.succ_eq]
      have hagreeN : ∀ i < n, δ'' i = extendTruePair δ'₀ i := by
        intro i hi
        simp [hδ''def, Function.update_of_ne (ne_of_lt hi)]
      have hbit : δ'' n = (b1, b2) := by simp [hδ''def]
      rw [atomPairG.congr D₀ D₁ splitY splitX X Y hagreeN, hbit]
      exact hz'
    rw [← hcover] at hδ'₀
    simp only [Set.mem_union] at hδ'₀
    rcases hδ'₀ with (h1 | h2) | (h3 | h4)
    · exact step true true h1
    · exact step true false h2
    · exact step false true h3
    · exact step false false h4

end AtomPairGen

end atomPairG
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace atomPairG

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section AtomPairGenDelta

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hySplit : SplitSpec' D₀ splitY)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hxSplit : SplitSpec' D₁ splitX)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hySplit hD₁pos hD₁diff hxSplit hXmem hYmem hD₀mne hD₁mne in
/-- **8.12(d)(4)(c)(iii): transporting the covering fact to a `deltaPair`-indexed one.** Combines
`(c)(ii)`'s `atomPairG.master_covered` (covering by `Fin n → Bool × Bool` histories) with
`encodeDeltaPair`/`deltaPair.encodeDeltaPair` (realizing any such history, padded via
`extendTruePair`, as a genuine bit-source) and `atomPairG.congr` (depth-`n` value depends only on
history strictly below `n`) to land on exactly the indexing `XPseqCode`'s fold uses. -/
theorem master_covered_deltaPair (n : ℕ) :
    ∀ z ∈ D₀.master, ∃ i < 4 ^ n, z ∈ (atomPairG D₀ D₁ splitY splitX X Y (deltaPair i) n).1 := by
  intro z hz
  obtain ⟨δ', hδ'⟩ := atomPairG.master_covered D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
    splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne n z hz
  refine ⟨encodeDeltaPair (extendTruePair δ') n, encodeDeltaPair_lt _ n, ?_⟩
  rw [atomPairG.congr D₀ D₁ splitY splitX X Y
    (fun i hi => deltaPair.encodeDeltaPair (extendTruePair δ') n i hi)]
  exact hδ'

end AtomPairGenDelta

end atomPairG
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace atomPairG

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section AtomPairGen

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hySplit : SplitSpec' D₀ splitY)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hxSplit : SplitSpec' D₁ splitX)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hySplit hD₁pos hD₁diff hxSplit hXmem hYmem hD₀mne hD₁mne

/-- **8.12(d)(4)(d)(i): the one-step 4-way classical reunion, `D₁`-side.** The `D₁`-side mirror of
`atomPairG.fst_union_step`: ranging over all four `(b1, b2) : Bool × Bool` sign choices at depth
`n`, the resulting depth-`(n+1)` `D₁`-pieces reunion to *exactly* the depth-`n` parent's `D₁`-piece.
Genuinely *simpler* to prove than the `D₀`-side version: here the *inner* (`b2`-level) collapse is
the hypothesis-free one (`yStepG.snd_union`, `D₁`'s side is `yStep`'s own direct-refine side) and
the *outer* (`b1`-level) collapse is the one needing `hxSplit` (`xStepG.snd_union`, `D₁`'s side is
`xStep`'s split side) — exactly the reverse pairing from the `D₀`-side proof, so no per-branch
`have`s (`hBAtrue`/`hAmemtrue`/etc.) are needed at all: `yStepG.snd_union` takes no `SplitSpec'`
hypotheses, so both inner collapses are immediate rewrites, leaving only the outer `xStepG.snd_union`
call. -/
theorem snd_union_step (δ : ℕ → Bool × Bool) (n : ℕ) :
    ((yStepG splitY (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) true).1
        (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) true).2 (Y n) true).2 ∪
      (yStepG splitY (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) true).1
        (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) true).2 (Y n) false).2) ∪
    ((yStepG splitY (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) false).1
        (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) false).2 (Y n) true).2 ∪
      (yStepG splitY (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) false).1
        (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) false).2 (Y n) false).2) =
      (atomPairG D₀ D₁ splitY splitX X Y δ n).2 := by
  obtain ⟨ihAB, ihA, ihB⟩ := atomPairG.invariant D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
    splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne δ n
  set A := (atomPairG D₀ D₁ splitY splitX X Y δ n).1 with hAdef
  set B := (atomPairG D₀ D₁ splitY splitX X Y δ n).2 with hBdef
  rw [yStepG.snd_union splitY (xStepG splitX A B (X n) true).1 (xStepG splitX A B (X n) true).2
      (Y n),
    yStepG.snd_union splitY (xStepG splitX A B (X n) false).1 (xStepG splitX A B (X n) false).2
      (Y n)]
  exact xStepG.snd_union hxSplit ihAB ihB (X n)

end AtomPairGen

end atomPairG
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace atomPairG

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section AtomPairGen

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hySplit : SplitSpec' D₀ splitY)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hxSplit : SplitSpec' D₁ splitX)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hySplit hD₁pos hD₁diff hxSplit hXmem hYmem hD₀mne hD₁mne

/-- **8.12(d)(4)(d)(ii): classical covering induction, `D₁`-side.** The `D₁`-side mirror of
`atomPairG.master_covered`: the classical `atomPairG` pieces at depth `n`, ranged over all
sign-histories `δ' : Fin n → Bool × Bool` (padded via `extendTruePair`), cover `D₁.master`. Verbatim
transcription of `atomPairG.master_covered`'s proof with `.1`→`.2`, `D₀.master`→`D₁.master`, and
`atomPairG.fst_union_step`→`atomPairG.snd_union_step`: induction on `n`, base case trivial
(`atomPairG _ 0 = (D₀.master, D₁.master)`), successor step extending a covering history by one more
`(b1, b2)` bit via the same `Function.update`/`restrictFinPair` device, picking whichever of the
four `atomPairG.snd_union_step` branches `z` landed in. -/
theorem master_covered_snd (n : ℕ) :
    ∀ z ∈ D₁.master, ∃ δ' : Fin n → Bool × Bool,
      z ∈ (atomPairG D₀ D₁ splitY splitX X Y (extendTruePair δ') n).2 := by
  induction n with
  | zero => exact fun z hz => ⟨Fin.elim0, hz⟩
  | succ n ih =>
    intro z hz
    obtain ⟨δ'₀, hδ'₀⟩ := ih z hz
    have hcover := atomPairG.snd_union_step D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
      splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne (extendTruePair δ'₀) n
    set A := (atomPairG D₀ D₁ splitY splitX X Y (extendTruePair δ'₀) n).1 with hAdef
    set B := (atomPairG D₀ D₁ splitY splitX X Y (extendTruePair δ'₀) n).2 with hBdef
    have step : ∀ b1 b2 : Bool,
        z ∈ (yStepG splitY (xStepG splitX A B (X n) b1).1 (xStepG splitX A B (X n) b1).2
          (Y n) b2).2 →
        ∃ δ' : Fin (n + 1) → Bool × Bool,
          z ∈ (atomPairG D₀ D₁ splitY splitX X Y (extendTruePair δ') (n + 1)).2 := by
      intro b1 b2 hz'
      set δ'' := Function.update (extendTruePair δ'₀) n (b1, b2) with hδ''def
      refine ⟨restrictFinPair δ'' (n + 1), ?_⟩
      have hagree : ∀ i < n + 1, extendTruePair (restrictFinPair δ'' (n + 1)) i = δ'' i :=
        fun i hi => extendTruePair_restrictFinPair_agree δ'' (n + 1) i hi
      rw [atomPairG.congr D₀ D₁ splitY splitX X Y hagree, atomPairG.succ_eq]
      have hagreeN : ∀ i < n, δ'' i = extendTruePair δ'₀ i := by
        intro i hi
        simp [hδ''def, Function.update_of_ne (ne_of_lt hi)]
      have hbit : δ'' n = (b1, b2) := by simp [hδ''def]
      rw [atomPairG.congr D₀ D₁ splitY splitX X Y hagreeN, hbit]
      exact hz'
    rw [← hcover] at hδ'₀
    simp only [Set.mem_union] at hδ'₀
    rcases hδ'₀ with (h1 | h2) | (h3 | h4)
    · exact step true true h1
    · exact step true false h2
    · exact step false true h3
    · exact step false false h4

end AtomPairGen

end atomPairG
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace atomPairG

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section AtomPairGenDelta

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hySplit : SplitSpec' D₀ splitY)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hxSplit : SplitSpec' D₁ splitX)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hySplit hD₁pos hD₁diff hxSplit hXmem hYmem hD₀mne hD₁mne in
/-- **8.12(d)(4)(d)(iii): transporting the covering fact to a `deltaPair`-indexed one, `D₁`-side.**
The `D₁`-side mirror of `atomPairG.master_covered_deltaPair`: combines `(d)(ii)`'s
`atomPairG.master_covered_snd` (covering by `Fin n → Bool × Bool` histories) with
`encodeDeltaPair`/`deltaPair.encodeDeltaPair` (realizing any such history, padded via
`extendTruePair`, as a genuine bit-source) and `atomPairG.congr` to land on exactly the indexing
`YPseqCode`'s fold uses. Verbatim transcription of `atomPairG.master_covered_deltaPair`'s proof,
swapping `.1`→`.2`, `D₀.master`→`D₁.master`, `atomPairG.master_covered`→`atomPairG.master_covered_snd`
— no new base-4 encoding needed, since `encodeDeltaPair`/`deltaPair` are already symmetric in
`.1`/`.2`. -/
theorem master_covered_deltaPair_snd (n : ℕ) :
    ∀ z ∈ D₁.master, ∃ i < 4 ^ n, z ∈ (atomPairG D₀ D₁ splitY splitX X Y (deltaPair i) n).2 := by
  intro z hz
  obtain ⟨δ', hδ'⟩ := atomPairG.master_covered_snd D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos
    hD₁diff splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne n z hz
  refine ⟨encodeDeltaPair (extendTruePair δ') n, encodeDeltaPair_lt _ n, ?_⟩
  rw [atomPairG.congr D₀ D₁ splitY splitX X Y
    (fun i hi => deltaPair.encodeDeltaPair (extendTruePair δ') n i hi)]
  exact hδ'

end AtomPairGenDelta

end atomPairG
end DomainTheory.NeighbourhoodSystems

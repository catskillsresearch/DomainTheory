/-ai
The four second components at depth n + 1, one for each pair of Boolean choices, reunite exactly to the second component at depth n.

The invariant supplies the preconditions of the X split. Each pair of Y steps reunites on the second component, and the two resulting X-step second components reunite to the parent.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableSplit
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableDiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableUnion
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xStepG
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.yStepG
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.yStepG_snd_union
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xStepG_snd_union
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairG
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairG_invariant

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.mem_ne_empty
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

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hySplit hD₁pos hD₁diff hxSplit hXmem hYmem hD₀mne hD₁mne

/-- **8.12(d)(4)(d)(i): the one-step 4-way classical reunion, `D₁`-side.** The `D₁`-side mirror of
`atomPairG_fst_union_step`: ranging over all four `(b1, b2) : Bool × Bool` sign choices at depth
`n`, the resulting depth-`(n+1)` `D₁`-pieces reunion to *exactly* the depth-`n` parent's `D₁`-piece.
Genuinely *simpler* to prove than the `D₀`-side version: here the *inner* (`b2`-level) collapse is
the hypothesis-free one (`yStepG_snd_union`, `D₁`'s side is `yStep`'s own direct-refine side) and
the *outer* (`b1`-level) collapse is the one needing `hxSplit` (`xStepG_snd_union`, `D₁`'s side is
`xStep`'s split side) — exactly the reverse pairing from the `D₀`-side proof, so no per-branch
`have`s (`hBAtrue`/`hAmemtrue`/etc.) are needed at all: `yStepG_snd_union` takes no `SplitSpec'`
hypotheses, so both inner collapses are immediate rewrites, leaving only the outer `xStepG_snd_union`
call. -/
theorem atomPairG_snd_union_step (δ : ℕ → Bool × Bool) (n : ℕ) :
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
  obtain ⟨ihAB, ihA, ihB⟩ := atomPairG_invariant D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
    splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne δ n
  set A := (atomPairG D₀ D₁ splitY splitX X Y δ n).1 with hAdef
  set B := (atomPairG D₀ D₁ splitY splitX X Y δ n).2 with hBdef
  rw [yStepG_snd_union splitY (xStepG splitX A B (X n) true).1 (xStepG splitX A B (X n) true).2
      (Y n),
    yStepG_snd_union splitY (xStepG splitX A B (X n) false).1 (xStepG splitX A B (X n) false).2
      (Y n)]
  exact xStepG_snd_union hxSplit ihAB ihB (X n)

end AtomPairGen

end DomainTheory.NeighbourhoodSystems

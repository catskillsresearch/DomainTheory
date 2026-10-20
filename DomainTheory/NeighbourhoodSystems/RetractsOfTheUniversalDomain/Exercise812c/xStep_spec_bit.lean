/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.extendTruePair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.restrictFinPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.extendTruePair_restrictFinPair_agree
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.xStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.atomPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.atomPair_congr
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.xStep_spec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.NoMinimal
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.DiffClosed

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

/-- **`xStep_spec_bit`** (8.12(c)(vi)(4)(c)): a drop-in generalization of `xStep_spec` to an
*arbitrary* bit `bx`, not just `δ n`'s own first component — the `SplitSpec'` preconditions `yStep`
needs, transported across the `X`-sub-step at bit `bx`, for *any* history `δ`. Proved by
transporting `xStep_spec` itself across a `Function.update`-adjusted history `δ''` that agrees with
`δ` below `n` and has `(δ'' n).1 = bx` exactly — the two-sided analogue of `Theorem88.lean`'s
`Function.update`-based `δ2` device in `split_fst_eq_inter_Yseq`. -/
theorem xStep_spec_bit (δ : ℕ → Bool × Bool) (n : ℕ) (bx : Bool) :
    ((xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
        (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) bx).2 = ∅ ↔
      (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
        (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) bx).1 = ∅) ∧
      ((xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
          (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) bx).1 = ∅ ∨
        D₀.mem (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
          (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) bx).1) := by
  set δ'' := Function.update (extendTruePair (restrictFinPair δ n)) n (bx, true) with hδ''def
  have hagree : ∀ i < n, δ'' i = δ i := by
    intro i hi
    have h1 : δ'' i = (extendTruePair (restrictFinPair δ n)) i := by
      simp [hδ''def, Function.update_of_ne (ne_of_lt hi)]
    rw [h1]; exact extendTruePair_restrictFinPair_agree δ n i hi
  have hbit : (δ'' n).1 = bx := by simp [hδ''def]
  have hcongr : atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ'' n =
      atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n := atomPair_congr D₀ D₁ hD₀nomin hD₁nomin X Y hagree
  have hspec := xStep_spec D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem
    hD₀mne hD₁mne δ'' n
  rwa [hcongr, hbit] at hspec

end AtomPair

end DomainTheory.NeighbourhoodSystems

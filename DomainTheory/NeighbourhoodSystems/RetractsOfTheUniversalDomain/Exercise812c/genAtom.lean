module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.IsEffectivelyGiven
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.part_c_2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.inter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.xStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.atomPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.atomPair_2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.combinedX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtomDecidable.DAtom_eq_empty_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCode_disjoint_YseqCode_of_posTwin_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCode_succ_true
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.hcoreIdxYc
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.transfer_dir_idxYc
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.xStep_3
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.combinedY

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
namespace genAtom

open NeighborhoodSystem

/-- **`genAtom`'s own recursive equation, as a rewritable lemma** (mirrors `Theorem88.lean`'s
`atomU_succ`; `genAtom`'s `def` is a direct structural match on its `Nat` argument, so this holds by
`rfl`, but stating it separately lets `rw` fire on `Nat`-literal successor forms like `2 * n + 1 + 1`
without needing to unfold `genAtom` itself). -/
theorem succ' {γ : Type*} (Z : ℕ → Set γ) (M : Set γ) (δ : ℕ → Bool) (n : ℕ) :
    genAtom Z M δ (n + 1) = genAtom Z M δ n ∩ (if δ n then Z n else M \ Z n) := rfl

end genAtom
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace genAtom

open NeighborhoodSystem

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

end AtomPair

end genAtom
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace genAtom

open NeighborhoodSystem

section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

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

end genAtom
end DomainTheory.NeighbourhoodSystems

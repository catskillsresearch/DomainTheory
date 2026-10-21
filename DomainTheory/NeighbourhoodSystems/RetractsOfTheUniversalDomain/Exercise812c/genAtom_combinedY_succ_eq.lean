/-ai
If the second component of atomPair at depth n agrees with the generic atom of combinedY at depth 2n, then the generic atom at depth 2n+1 equals the second output of the X-step at the first sign bit.

The successor law of the generic atom, the assumed agreement, and the even clauses of the interleaved signs and of combinedY reduce the claim to the two-branch closed form of that second output, read in reverse.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.genAtom_succ'
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.xStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.atomPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.xStep_snd_succ_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.combinedY
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.combinedδ
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.combinedY_even
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.combinedδ_even
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.NoMinimal
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.DiffClosed

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.IsEffectivelyGiven
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

/-- **The odd-depth half-step identity for `combinedY`**: given `atomPair δ n`'s `β`-side agrees
with `genAtom combinedY` at the even depth `2 * n`, it also agrees at the odd depth `2 * n + 1` with
the `X`-sub-step's own (choice-split) `β`-side output — via (vi)(5)(a)'s closed form
`xStep_snd_succ_eq`, run at `combinedδ`/`combinedX`'s even value `(δ n).1`. -/
theorem genAtom_combinedY_succ_eq (δ : ℕ → Bool × Bool) (n : ℕ)
    (hn : (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 =
      genAtom (combinedY D₀ D₁ hD₀nomin hD₁nomin X Y) D₁.master (combinedδ δ) (2 * n)) :
    genAtom (combinedY D₀ D₁ hD₀nomin hD₁nomin X Y) D₁.master (combinedδ δ) (2 * n + 1) =
      (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
        (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) (δ n).1).2 := by
  rw [genAtom_succ', ← hn, combinedδ_even, combinedY_even]
  exact (xStep_snd_succ_eq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem
    hD₀mne hD₁mne δ n (δ n).1).symm

end AtomPair

end DomainTheory.NeighbourhoodSystems

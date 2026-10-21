/-ai
The first component of atomPair at every depth is contained in the master of D₀.

The proof is by induction on the depth. At depth zero the component is the master, so the inclusion is reflexive. At a successor the one-step inclusion is composed with the inductive inclusion.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.atomPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.atomPair_fst_subset
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

/-- **`atomPair`'s `α`-side is always `⊆ D₀.master`** (by induction from the base case
`atomPair δ 0 = D₀.master`, shrinking at each step via `atomPair_fst_subset`). Placed here
(rather than alongside 8.12(c)(vi)(5)'s other consumers below) since 8.12(c)(vi)(5)(a)'s
`xStep_snd_succ_eq`/`yStep_fst_succ_eq` closed forms need it too, and both only depend on
`atomPair_fst_subset`/`atomPair_snd_subset` just above — no need to wait for `atomPair_disjoint`
or `XPseq`/`YPseq`. -/
theorem atomPair_fst_subset_master (δ : ℕ → Bool × Bool) (n : ℕ) :
    (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1 ⊆ D₀.master := by
  induction n with
  | zero => exact subset_rfl
  | succ n ih => exact (atomPair_fst_subset D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin
      X Y hXmem hYmem hD₀mne hD₁mne δ n).trans ih

end AtomPair

end DomainTheory.NeighbourhoodSystems

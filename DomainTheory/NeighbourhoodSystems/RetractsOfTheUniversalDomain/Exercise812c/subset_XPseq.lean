module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.extendTruePair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.xStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.atomPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.XPseq
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

omit hD₀pos hD₀diff hD₁pos hD₁diff hXmem hYmem hD₀mne hD₁mne in
theorem subset_XPseq {n : ℕ} (δ' : Fin n → Bool × Bool) :
    (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y (extendTruePair δ') n).1
      (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y (extendTruePair δ') n).2 (X n) true).2 ⊆
      XPseq D₀ D₁ hD₀nomin hD₁nomin X Y n :=
  Set.subset_iUnion
    (fun δ' => (xStep D₁ hD₁nomin
      (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y (extendTruePair δ') n).1
      (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y (extendTruePair δ') n).2 (X n) true).2) δ'

end AtomPair

end DomainTheory.NeighbourhoodSystems

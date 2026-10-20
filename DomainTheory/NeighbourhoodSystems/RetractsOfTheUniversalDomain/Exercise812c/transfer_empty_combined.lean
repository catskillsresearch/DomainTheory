module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.combinedX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.combinedY
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.hcore
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

theorem transfer_empty_combined {cs : List (ℕ × Bool)} {n : ℕ} (hn : ∀ p ∈ cs, p.1 < n) :
    {x ∈ D₀.master | ∀ p ∈ cs, (p.2 = true ↔ x ∈ combinedX D₀ D₁ hD₀nomin hD₁nomin X Y p.1)}.Nonempty ↔
      {y ∈ D₁.master |
        ∀ p ∈ cs, (p.2 = true ↔ y ∈ combinedY D₀ D₁ hD₀nomin hD₁nomin X Y p.1)}.Nonempty := by
  have hc := hcore D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem hD₀mne
    hD₁mne
  have hc' : ∀ δ n, genAtom (combinedY D₀ D₁ hD₀nomin hD₁nomin X Y) D₁.master δ n = ∅ ↔
      genAtom (combinedX D₀ D₁ hD₀nomin hD₁nomin X Y) D₀.master δ n = ∅ :=
    fun δ n => (hc δ n).symm
  exact ⟨transfer_dir (combinedX D₀ D₁ hD₀nomin hD₁nomin X Y) D₀.master
      (combinedY D₀ D₁ hD₀nomin hD₁nomin X Y) D₁.master hc hn,
    transfer_dir (combinedY D₀ D₁ hD₀nomin hD₁nomin X Y) D₁.master
      (combinedX D₀ D₁ hD₀nomin hD₁nomin X Y) D₀.master hc' hn⟩

end AtomPair

end DomainTheory.NeighbourhoodSystems

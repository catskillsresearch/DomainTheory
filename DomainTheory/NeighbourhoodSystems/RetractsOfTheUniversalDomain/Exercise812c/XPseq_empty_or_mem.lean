/-ai
XPseq n is empty or a neighbourhood of the second system.

Apply finite-union closure in that system. For each finite sign sequence, the atom-pair invariant of the padded sequence gives the emptiness agreement and the membership alternative on the second side, and the first clause of the splitting specification for the choice split of that system against X n is the required empty-or-membership alternative.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.splitChoice'_isSplitSpec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.extendTruePair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.iUnion_mem_or_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.atomPair_invariant
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.XPseq
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

/-- **`XPseq n` is always `∅` or a genuine `D₁`-neighbourhood.** -/
theorem XPseq_empty_or_mem (n : ℕ) :
    XPseq D₀ D₁ hD₀nomin hD₁nomin X Y n = ∅ ∨ D₁.mem (XPseq D₀ D₁ hD₀nomin hD₁nomin X Y n) := by
  apply iUnion_mem_or_empty hD₁pos hD₁diff
  intro δ'
  obtain ⟨hAB, -, hBmem⟩ := atomPair_invariant D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff
    hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne (extendTruePair δ') n
  exact (splitChoice'_isSplitSpec D₁ hD₁nomin hAB hBmem (X n)).1

end AtomPair

end DomainTheory.NeighbourhoodSystems

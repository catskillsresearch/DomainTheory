/-ai
Re-interleaving the de-interleaving of a Boolean sequence returns the original sequence.

Extensionality reduces the claim to an arbitrary index. Unfolding both maps and splitting on the parity of that index, the doubled half-index, or that quantity plus one, equals the original index.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.combinedδ
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.deinterleaveδ
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.NoMinimal
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.DiffClosed

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.IsEffectivelyGiven
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtomDecidable.DAtomEmptyChar_eq_one_iff
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

omit hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne in
/-- **Round-trip identity** (Exercise 8.12(c)(vi)(5)(c)(1)): re-interleaving `deinterleaveδ δ'`
recovers `δ'` exactly. Proved by `funext` plus a parity case split on the point `m`, closed by
`combinedδ_even`/`combinedδ_odd` and `omega`. -/
theorem combinedδ_deinterleaveδ (δ' : ℕ → Bool) :
    combinedδ (deinterleaveδ δ') = δ' := by
  funext m
  unfold combinedδ deinterleaveδ
  split
  · rename_i hm
    rw [show 2 * (m / 2) = m from by omega]
  · rename_i hm
    rw [show 2 * (m / 2) + 1 = m from by omega]

end AtomPair

end DomainTheory.NeighbourhoodSystems

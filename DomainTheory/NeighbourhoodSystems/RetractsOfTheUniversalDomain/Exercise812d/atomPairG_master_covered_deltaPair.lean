/-ai
Every point of the master neighbourhood of the first neighbourhood system lies, at depth n, in the first component of the generalized atom pair along the bit history of some bit-source strictly below 4 to the n.

A finite history is taken from the covering theorem and encoded as a bit-source below 4 to the n. Congruence applies because the decoded history of that code agrees with the padded finite history at every position below n.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableSplit
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableDiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableUnion
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairG
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairG_congr
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairG_master_covered
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx0_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx1_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateJunk_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateRemC_packStateC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateInnerC_packStateC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.deltaPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.encodeDeltaPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.encodeDeltaPair_lt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.deltaPair_encodeDeltaPair

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.mem_ne_empty
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

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
`(c)(ii)`'s `atomPairG_master_covered` (covering by `Fin n → Bool × Bool` histories) with
`encodeDeltaPair`/`deltaPair_encodeDeltaPair` (realizing any such history, padded via
`extendTruePair`, as a genuine bit-source) and `atomPairG_congr` (depth-`n` value depends only on
history strictly below `n`) to land on exactly the indexing `XPseqCode`'s fold uses. -/
theorem atomPairG_master_covered_deltaPair (n : ℕ) :
    ∀ z ∈ D₀.master, ∃ i < 4 ^ n, z ∈ (atomPairG D₀ D₁ splitY splitX X Y (deltaPair i) n).1 := by
  intro z hz
  obtain ⟨δ', hδ'⟩ := atomPairG_master_covered D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
    splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne n z hz
  refine ⟨encodeDeltaPair (extendTruePair δ') n, encodeDeltaPair_lt _ n, ?_⟩
  rw [atomPairG_congr D₀ D₁ splitY splitX X Y
    (fun i hi => deltaPair_encodeDeltaPair (extendTruePair δ') n i hi)]
  exact hδ'

end AtomPairGenDelta

end DomainTheory.NeighbourhoodSystems

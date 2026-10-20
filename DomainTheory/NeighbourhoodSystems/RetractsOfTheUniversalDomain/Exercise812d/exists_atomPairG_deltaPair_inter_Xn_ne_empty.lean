module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableSplit
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableDiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableUnion
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairG
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx0_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx1_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateJunk_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateRemC_packStateC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateInnerC_packStateC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.deltaPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairG_master_covered_deltaPair

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section AtomPairCorrect4

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty) (hD₀nomin : D₀.NoMinimal)

include hD₀pos hD₀diff hxSplit hD₁pos hD₁diff hySplit hD₀mne hD₁mne hD₀nomin in
/-- **8.12(d)(4)(c)(iv): non-trivial intersection with `P₀.X n`, still classical.** Combines
`(c)(iii)`'s `atomPairG_master_covered_deltaPair` with `P₀.X n ⊆ D₀.master` (`sub_master`) and
`P₀.X n ≠ ∅` (fresh here: `hD₀nomin.mem_ne_empty`, the one place in `(d)(4)(c)`'s whole closure that
needs `NoMinimal` itself, rather than just `SplitSpec'`/`IsPositive`/`DiffClosed` — `(d)(1)`'s
generalized layer deliberately dropped `NoMinimal`, but this specific fact ("every genuine
neighbourhood, not just the master, is non-empty") has no substitute among the weaker hypotheses).
Picks any `z ∈ P₀.X n` (exists by the above), lands it in some covering piece via `(c)(iii)`, and
that piece's `i` is exactly the witness. -/
theorem exists_atomPairG_deltaPair_inter_Xn_ne_empty (n : ℕ) :
    ∃ i < 4 ^ n, (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1 ∩ P₀.X n ≠ ∅ := by
  obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr (hD₀nomin.mem_ne_empty (P₀.mem_X n))
  have hzmaster : z ∈ D₀.master := D₀.sub_master (P₀.mem_X n) hz
  obtain ⟨i, hi, hzcover⟩ := atomPairG_master_covered_deltaPair D₀ D₁ hD₀pos hD₀diff splitY hySplit
    hD₁pos hD₁diff splitX hxSplit P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne n z hzmaster
  exact ⟨i, hi, Set.nonempty_iff_ne_empty.mp ⟨z, hzcover, hz⟩⟩

end AtomPairCorrect4

end DomainTheory.NeighbourhoodSystems

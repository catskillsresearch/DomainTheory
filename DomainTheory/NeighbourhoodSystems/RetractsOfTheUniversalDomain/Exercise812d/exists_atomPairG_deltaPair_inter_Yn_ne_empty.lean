/-ai
For every code n there is a bit-source below four to the n whose second atom-pair component meets the second presentation's enumerated neighbourhood of n.

That neighbourhood is nonempty, so it has a point, and the point lies in the master of the second system. The second-component covering theorem places the point in the second component of the atom pair of some bit-source below four to the n, and that point witnesses a nonempty intersection.
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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx0_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx1_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateJunk_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateRemC_packStateC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateInnerC_packStateC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.deltaPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairG_master_covered_deltaPair_snd

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section AtomPairCorrect4Snd

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty) (hD₁nomin : D₁.NoMinimal)

include hD₀pos hD₀diff hxSplit hD₁pos hD₁diff hySplit hD₀mne hD₁mne hD₁nomin in
/-- **8.12(d)(4)(d)(iv): non-trivial intersection with `P₁.X n`, still classical, `D₁`-side.** The
`D₁`-side mirror of `(c)(iv)`'s `exists_atomPairG_deltaPair_inter_Xn_ne_empty`: combines `(d)(iii)`'s
`atomPairG_master_covered_deltaPair_snd` with `P₁.X n ⊆ D₁.master` (`sub_master`) and `P₁.X n ≠ ∅`
(fresh `hD₁nomin.mem_ne_empty`, the `D₁`-side analogue of `(c)(iv)`'s one genuinely new hypothesis).
Picks any `z ∈ P₁.X n` (exists by the above), lands it in some covering piece via `(d)(iii)`, and
that piece's `i` is exactly the witness. Note this alone doesn't fix the `bx` bit `YPseqCode`'s fold
also needs — that's resolved only in `(d)(vi)`. -/
theorem exists_atomPairG_deltaPair_inter_Yn_ne_empty (n : ℕ) :
    ∃ i < 4 ^ n, (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 ∩ P₁.X n ≠ ∅ := by
  obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr (hD₁nomin.mem_ne_empty (P₁.mem_X n))
  have hzmaster : z ∈ D₁.master := D₁.sub_master (P₁.mem_X n) hz
  obtain ⟨i, hi, hzcover⟩ := atomPairG_master_covered_deltaPair_snd D₀ D₁ hD₀pos hD₀diff splitY
    hySplit hD₁pos hD₁diff splitX hxSplit P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne n z hzmaster
  exact ⟨i, hi, Set.nonempty_iff_ne_empty.mp ⟨z, hzcover, hz⟩⟩

end AtomPairCorrect4Snd

end DomainTheory.NeighbourhoodSystems

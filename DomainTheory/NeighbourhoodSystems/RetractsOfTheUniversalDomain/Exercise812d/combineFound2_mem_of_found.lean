/-ai
If the combined found flag is 1, the image of the combined code is a genuine neighbourhood, assuming each input code is genuine when its own flag is 1.

The combination is unfolded. A zero first flag returns the second code. A first flag of 1 and a zero second flag return the first code. Both flags equal to 1 return the union index of two genuine neighbourhoods, which is itself genuine.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableSplit
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableDiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableUnion
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx0_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx1_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateJunk_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateRemC_packStateC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateInnerC_packStateC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.mem_union_of_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.combineFound2

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.mem_ne_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.union_mem_or_empty
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

theorem combineFound2_mem_of_found {γ : Type*} {W : NeighborhoodSystem γ}
    {Q : ComputablePresentation W} (hpos : W.IsPositive) (hdiff : W.DiffClosed)
    (hnomin : W.NoMinimal) (hUnion : IsComputableUnion Q) {r0 r1 : ℕ}
    (h0 : r0.unpair.1 ≤ 1) (h1 : r1.unpair.1 ≤ 1)
    (hmem0 : r0.unpair.1 = 1 → W.mem (Q.X r0.unpair.2))
    (hmem1 : r1.unpair.1 = 1 → W.mem (Q.X r1.unpair.2)) :
    (combineFound2 hUnion r0 r1).unpair.1 = 1 →
      W.mem (Q.X (combineFound2 hUnion r0 r1).unpair.2) := by
  unfold combineFound2
  rcases Nat.eq_zero_or_pos r0.unpair.1 with hr0 | hr0
  · rw [hr0, selectFn_zero]
    exact hmem1
  · rw [show r0.unpair.1 = 1 from by omega, selectFn_one]
    have hmem0' := hmem0 (by omega)
    rcases Nat.eq_zero_or_pos r1.unpair.1 with hr1 | hr1
    · rw [hr1, selectFn_zero]
      exact fun _ => hmem0'
    · rw [show r1.unpair.1 = 1 from by omega, selectFn_one, unpair_pair_snd]
      intro _
      have hmem1' := hmem1 (by omega)
      have hex : ∃ k, Q.X k = Q.X r0.unpair.2 ∪ Q.X r1.unpair.2 :=
        Q.surj (NeighborhoodSystem.mem_union_of_mem hpos hdiff hnomin hmem0' hmem1')
      rw [hUnion.unionIdx_spec hex]
      exact NeighborhoodSystem.mem_union_of_mem hpos hdiff hnomin hmem0' hmem1'

end DomainTheory.NeighbourhoodSystems

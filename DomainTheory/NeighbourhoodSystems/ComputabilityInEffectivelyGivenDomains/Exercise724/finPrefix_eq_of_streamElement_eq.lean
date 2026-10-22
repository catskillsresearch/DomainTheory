module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.LFunData
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.BasicInst2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.cons_inl
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.cons_inr
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.L_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.L_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.finPrefix
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.finPrefix_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.finPrefix_length
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.finPrefix_take
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.streamElement

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise724

open NeighborhoodSystem Domain.Recursive

/-- **Prefixes match on the nose whenever the stream elements agree.** -/
theorem finPrefix_eq_of_streamElement_eq {f₁ f₂ : ℕ → ℕ} (heq : streamElement f₁ = streamElement f₂) :
    ∀ n, finPrefix f₁ n = finPrefix f₂ n := by
  intro n
  have hmem1 : (streamElement f₁).mem (nbhd (finPrefix f₁ n)) := ⟨mem_nbhd _, n, subset_rfl⟩
  rw [heq] at hmem1
  obtain ⟨-, m, hm⟩ := hmem1
  have hpre : finPrefix f₁ n <+: finPrefix f₂ m := (nbhd_subset_iff _ _).mp hm
  have hlen : n ≤ m := by
    have hl := hpre.length_le; rwa [finPrefix_length, finPrefix_length] at hl
  have hpre' : finPrefix f₁ n = (finPrefix f₂ m).take (finPrefix f₁ n).length :=
    List.prefix_iff_eq_take.mp hpre
  rw [finPrefix_length] at hpre'
  rw [hpre', finPrefix_take f₂ hlen]

end DomainTheory.NeighbourhoodSystems.Exercise724

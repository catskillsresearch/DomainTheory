module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.EffectiveIso
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.mem_fiber2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2_reindexF
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber_reindexG
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Fmap_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Gmap
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Gmap_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2_iterEnum_iter

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.NeighborhoodSystemu2eIsEffectivelyGivenu2etoS
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashMap_isComputable
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashProju2080_isComputable
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashProju2081_isComputable
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise718

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β : Type*}

variable {V : NeighborhoodSystem α}

variable (P : ComputablePresentation V)

variable {P}

/-- **Characterisation of `G`'s relation on codes.** A single bounded inclusion: only `k < n`
matters (the codomain fiber is `Δ` for `k ≥ n`). -/
theorem Gmap_rel_enum_iff (s n : ℕ) :
    (Gmap V).rel (iterEnum (iterPresentation P) s) (iterEnum P n) ↔
      ∀ k, k < n →
        P.X (iterIdx P (iterIdx (iterPresentation P) s (Nat.unpair k).1) (Nat.unpair k).2)
          ⊆ P.X (iterIdx P n k) := by
  rw [Gmap_rel]
  have hmem₁ := iterEnum_mem (P := iterPresentation P) s
  have hmem₂ := iterEnum_mem (P := P) n
  constructor
  · rintro ⟨-, -, hg⟩ k _
    have := hg k
    rwa [fiber2_iterEnum_iter, fiber_iterEnum] at this
  · intro hbd
    refine ⟨hmem₁, hmem₂, fun k => ?_⟩
    rw [fiber2_iterEnum_iter, fiber_iterEnum]
    by_cases hk : k < n
    · exact hbd k hk
    · rw [iterIdx_ge (not_lt.mp hk), P.masterIdx_spec]
      exact V.sub_master (P.mem_X _)

end Exercise718

end DomainTheory.NeighbourhoodSystems

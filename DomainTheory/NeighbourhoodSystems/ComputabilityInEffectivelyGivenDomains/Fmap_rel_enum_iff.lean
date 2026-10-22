module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.EffectiveIso
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.mem_fiber2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2_reindexF
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber_reindexG
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Fmap
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Fmap_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Gmap_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2_iterEnum_iter
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.masterIdx_iterPresentation

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

/-- **Characterisation of `F`'s relation on codes.** Relative to `iterPresentation P` and
`iterPresentation (iterPresentation P)`, the relation reduces to a *bounded* double inclusion:
beyond the coded fiber lengths every fiber is `Δ`, so only `i < m` and `j < iterIdx (iterᴾ) m i`
matter. -/
theorem Fmap_rel_enum_iff (n m : ℕ) :
    (Fmap V).rel (iterEnum P n) (iterEnum (iterPresentation P) m) ↔
      ∀ i, i < m → ∀ j, j < iterIdx (iterPresentation P) m i →
        P.X (iterIdx P n (Nat.pair i j)) ⊆ P.X (iterIdx P (iterIdx (iterPresentation P) m i) j) := by
  rw [Fmap_rel]
  have hmem₁ := iterEnum_mem (P := P) n
  have hmem₂ := iterEnum_mem (P := iterPresentation P) m
  constructor
  · rintro ⟨-, -, hf⟩ i _ j _
    have := hf i j
    rwa [fiber_iterEnum, fiber2_iterEnum_iter] at this
  · intro hbd
    refine ⟨hmem₁, hmem₂, fun i j => ?_⟩
    rw [fiber_iterEnum, fiber2_iterEnum_iter]
    by_cases hi : i < m
    · by_cases hj : j < iterIdx (iterPresentation P) m i
      · exact hbd i hi j hj
      · -- `j` beyond the inner length ⟹ RHS `= Δ`
        rw [iterIdx_ge (not_lt.mp hj), P.masterIdx_spec]
        exact V.sub_master (P.mem_X _)
    · -- `i` beyond the outer length ⟹ inner code `= 0` ⟹ RHS `= Δ`
      have h0 : iterIdx (iterPresentation P) m i = 0 := by
        rw [iterIdx_ge (not_lt.mp hi), masterIdx_iterPresentation]
      rw [h0, iterIdx_ge (Nat.zero_le j), P.masterIdx_spec]
      exact V.sub_master (P.mem_X _)

end Exercise718

end DomainTheory.NeighbourhoodSystems

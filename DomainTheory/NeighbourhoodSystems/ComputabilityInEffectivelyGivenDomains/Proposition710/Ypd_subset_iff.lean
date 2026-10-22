module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.UPX_def
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.Ypd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.Ypd_def
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.upSet_subset_Ypd_iff

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

variable (P : ComputablePresentation V)

/-- `Y_c ⊆ Y_k ↔ ∀ a ∈ dl c, ∃ b ∈ dl k, X_a ⊆ X_b`. -/
theorem Ypd_subset_iff {c k : ℕ} :
    V.Ypd P c ⊆ V.Ypd P k ↔ ∀ a ∈ decodeList c, ∃ b ∈ decodeList k, P.X a ⊆ P.X b := by
  rw [Ypd_def, UPX_def, Set.iUnion₂_subset_iff]
  constructor
  · intro h a ha; exact (V.upSet_subset_Ypd_iff P).mp (h a ha)
  · intro h a ha; exact (V.upSet_subset_Ypd_iff P).mpr (h a ha)

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems

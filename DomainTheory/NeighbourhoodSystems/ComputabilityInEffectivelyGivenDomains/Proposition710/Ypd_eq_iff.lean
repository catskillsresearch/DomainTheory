module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.Ypd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.Ypd_subset_iff

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

variable (P : ComputablePresentation V)

/-- **Equality of two finite unions of down-sets**, unfolded as a nested bounded `∀/∃`. -/
theorem Ypd_eq_iff {c k : ℕ} :
    V.Ypd P c = V.Ypd P k ↔
      (∀ a ∈ decodeList c, ∃ b ∈ decodeList k, P.X a ⊆ P.X b) ∧
      (∀ b ∈ decodeList k, ∃ a ∈ decodeList c, P.X b ⊆ P.X a) := by
  rw [Set.Subset.antisymm_iff, V.Ypd_subset_iff P, V.Ypd_subset_iff P]

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems

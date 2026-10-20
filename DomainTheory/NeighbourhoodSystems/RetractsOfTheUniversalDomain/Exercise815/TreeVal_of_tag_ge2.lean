module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise714
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_finGenSys
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_nbhdGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_SubD
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.SubD_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.QBody
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.QFuel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.TreeVal

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}

section UniversalSubsystem

section TreeVal

variable (r : ℕ → ℕ)

/-- **Tag-`≥ 2` unfolding, for an arbitrary code.** -/
theorem TreeVal_of_tag_ge2 {c : ℕ} (h : 2 ≤ c.unpair.1) :
    TreeVal r c = UComputablePresentation.masterIdx := by
  have h1 : isOne (1 - c.unpair.1) = 0 := by
    have : (1 - c.unpair.1 : ℕ) = 0 := by omega
    rw [this]; rfl
  have h2 : isOne (2 - c.unpair.1) = 0 := by
    have : (2 - c.unpair.1 : ℕ) = 0 := by omega
    rw [this]; rfl
  show QBody r (QFuel r c) c = UComputablePresentation.masterIdx
  unfold QBody
  simp only [h1, h2, selectFn_zero]

end TreeVal

end UniversalSubsystem

end DomainTheory.NeighbourhoodSystems

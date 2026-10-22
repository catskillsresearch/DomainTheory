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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.masterCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.QBody
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.QFuel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.TreeVal

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}

section UniversalSubsystem

section TreeVal

variable (r : ℕ → ℕ)

/-- **Unfolding at the master constant.** -/
theorem TreeVal_master : TreeVal r masterCode = UComputablePresentation.masterIdx := by
  have htag : masterCode.unpair.1 = 2 := by unfold masterCode; rw [unpair_pair_fst]
  have h1 : isOne (1 - masterCode.unpair.1) = 0 := by rw [htag]; rfl
  have h2 : isOne (2 - masterCode.unpair.1) = 0 := by rw [htag]; rfl
  show QBody r (QFuel r masterCode) masterCode = UComputablePresentation.masterIdx
  unfold QBody
  simp only [h1, h2, selectFn_zero]

end TreeVal

end UniversalSubsystem

end DomainTheory.NeighbourhoodSystems

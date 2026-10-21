/-ai
Evaluation of a leaf code returns the enumerator at the index stored in the leaf.

The tag of a leaf code is zero and its payload is that index, so the first selector equals one and the fuel step returns the enumerator at the payload.
ai-/
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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.leafCode
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

/-- **Unfolding at a leaf.** -/
theorem TreeVal_leaf (j : ℕ) : TreeVal r (leafCode j) = r j := by
  have htag : (leafCode j).unpair.1 = 0 := by unfold leafCode; rw [unpair_pair_fst]
  have hpay : (leafCode j).unpair.2 = j := by unfold leafCode; rw [unpair_pair_snd]
  have h1 : isOne (1 - (leafCode j).unpair.1) = 1 := by rw [htag]; rfl
  show QBody r (QFuel r (leafCode j)) (leafCode j) = r j
  unfold QBody
  simp only [h1, hpay, selectFn_one]

end TreeVal

end UniversalSubsystem

end DomainTheory.NeighbourhoodSystems

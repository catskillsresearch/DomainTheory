module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise714
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_finGenSys
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.finGenSys_subsystem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.finGen_append_le_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.nbhdGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_nbhdGen

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}

section SubD

variable (P : ComputablePresentation D)

/-- **The concatenation identity for `nbhd`.** `nbhd(js₁) ∩ nbhd(js₂) = nbhd(js₁ ++ js₂)` —
`finGen_append_le_iff` instantiated at `D' := finGenSys(js')` for each candidate `js'`. -/
theorem nbhdGen_inter (js1 js2 : List ℕ) :
    nbhdGen P js1 ∩ nbhdGen P js2 = nbhdGen P (js1 ++ js2) := by
  apply Set.ext
  intro js'
  simp only [mem_nbhdGen, Set.mem_inter_iff]
  exact (finGen_append_le_iff P (finGenSys_subsystem P js') js1 js2).symm

end SubD

end DomainTheory.NeighbourhoodSystems

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise714
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.finGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_finGenSys
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.finGenSys_subsystem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.finGen_le_iff_forall_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_nbhdGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_SubD
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.SubD_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_finGen_computable

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}

section Computability

variable (P : ComputablePresentation D)

/-- **`Fin(decodeList c1) ⊆ Fin(decodeList c2)` is recursively decidable** — rewrite via
`finGen_le_iff_forall_mem` (at `D' := finGenSys P (decodeList c2)`, a genuine subsystem of `D` by
`finGenSys_subsystem`) to `∀ i ∈ decodeList c1, P.X i ∈ finGen P (decodeList c2)`, which is exactly
`mem_finGen_computable.bForallList`. -/
theorem finGen_subset_computable :
    RecDecidable₂ (fun c1 c2 => finGen P (decodeList c1) ⊆ finGen P (decodeList c2)) := by
  have hiff : ∀ c1 c2, finGen P (decodeList c1) ⊆ finGen P (decodeList c2) ↔
      ∀ i ∈ decodeList c1, P.X i ∈ finGen P (decodeList c2) :=
    fun c1 c2 => finGen_le_iff_forall_mem P (finGenSys_subsystem P (decodeList c2)) (decodeList c1)
  refine RecDecidable.of_iff (fun t => ?_) (mem_finGen_computable P).bForallList
  exact hiff t.unpair.1 t.unpair.2

end Computability

end DomainTheory.NeighbourhoodSystems

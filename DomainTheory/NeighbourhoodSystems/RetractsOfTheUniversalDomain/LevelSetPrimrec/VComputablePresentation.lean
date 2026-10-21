/-ai
The computable presentation of the neighbourhood system V, for Exercise 8.12(b),
enumerates neighbourhoods by the canonical level-set enumeration, with the membership
and surjectivity lemmas, the recursive decidability of intersection equality and of
consistency, the intersection index with its primitive recursiveness and its
specification, and the master index with its specification.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.VX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.V_mem_VX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.V_surj_VX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.V_interEq_computable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.V_cons_computable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.Vinter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.primrec_Vinter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.Vinter_spec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.VmasterIdx
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.VX_VmasterIdx

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **Exercise 8.12(b).** `V` (Exercise 8.12(a)) has a genuine `ComputablePresentation`. -/
def VComputablePresentation : ComputablePresentation V where
  X := VX
  mem_X := V_mem_VX
  surj := V_surj_VX
  interEq_computable := V_interEq_computable
  cons_computable := V_cons_computable
  inter := Vinter
  inter_primrec := primrec_Vinter
  inter_spec := Vinter_spec
  masterIdx := VmasterIdx
  masterIdx_spec := VX_VmasterIdx

end DomainTheory.NeighbourhoodSystems

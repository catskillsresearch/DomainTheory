/-ai
A computable presentation of the neighbourhood system U is the enumeration of canonicalized rational-pair codes, together with membership in U, surjectivity onto the neighbourhoods of U, recursive decidability of intersection equality and of consistency, a primitive-recursive intersection index, and a master index for the master neighbourhood.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.decodeRatPair_masterPairCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.UX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.U_mem_UX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.U_surj_UX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.U_interEq_computable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.U_cons_computable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.Uinter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.Uinter_primrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.Uinter_spec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.UmasterIdx
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.UX_UmasterIdx

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **Theorem 8.8(b), Part 3.** `𝒰` (Definition 8.7) has a genuine `ComputablePresentation`. -/
def UComputablePresentation : ComputablePresentation U where
  X := UX
  mem_X := U_mem_UX
  surj := U_surj_UX
  interEq_computable := U_interEq_computable
  cons_computable := U_cons_computable
  inter := Uinter
  inter_primrec := Uinter_primrec
  inter_spec := Uinter_spec
  masterIdx := UmasterIdx
  masterIdx_spec := UX_UmasterIdx

end DomainTheory.NeighbourhoodSystems

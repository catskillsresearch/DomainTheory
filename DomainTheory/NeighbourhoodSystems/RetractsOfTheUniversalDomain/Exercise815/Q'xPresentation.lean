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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.toSubsystemSys
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.masterCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.Q2X
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.Q2x_mem_X
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.Q2x_surj
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.Q2inter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.primrec_Q2inter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.Q2inter_spec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.Q2_interEq_computable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.Q2_cons_computable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.Q2X_masterIdx_spec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.SubD

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}

section UniversalSubsystem

section TreeVal2

variable (r : ℕ → ℕ) (x : (SubD UComputablePresentation).Element)

/-- **Subgoal 6f, capstone.** `D'x := toSubsystemSys UComputablePresentation x` admits a genuine
`ComputablePresentation`, assembled from `Q2X`/`Q2x_mem_X`/`Q2x_surj`/`Q2_interEq_computable`/
`Q2_cons_computable`/`Q2inter`/`Q2inter_spec`/`masterCode`/`Q2X_masterIdx_spec` — resolving the gap
flagged above via the binary term algebra. -/
def Q'xPresentation (hr : Nat.Primrec r)
    (hspec : ∀ i, (toSubsystemSys UComputablePresentation x).mem (UX i) ↔ ∃ n, r n = i) :
    ComputablePresentation (toSubsystemSys UComputablePresentation x) where
  X := Q2X r
  mem_X := Q2x_mem_X r x hspec
  surj := Q2x_surj r x hspec
  interEq_computable := Q2_interEq_computable r hr
  cons_computable := Q2_cons_computable r hr
  inter := Q2inter
  inter_primrec := primrec_Q2inter
  inter_spec := fun h => Q2inter_spec r h
  masterIdx := masterCode
  masterIdx_spec := Q2X_masterIdx_spec r x

end TreeVal2

end UniversalSubsystem

end DomainTheory.NeighbourhoodSystems

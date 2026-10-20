module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.primrec_VdiffRaw
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Vdiff

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem primrec_Vdiff : Nat.Primrec (fun t => Vdiff t.unpair.1 t.unpair.2) :=
  (primrec_canonIdx.comp primrec_VdiffRaw).of_eq fun _ => rfl

end DomainTheory.NeighbourhoodSystems

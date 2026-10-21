/-ai
The function sending a paired natural number to the canonical union of its two components is primitive recursive.

It is the canonical-index function composed with the raw union, and the composite agrees with the definition by reflexivity.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.primrec_VunionRaw
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Vunion

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.UnionClosed
@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem primrec_Vunion : Nat.Primrec (fun t => Vunion t.unpair.1 t.unpair.2) :=
  (primrec_canonIdx.comp primrec_VunionRaw).of_eq fun _ => rfl

end DomainTheory.NeighbourhoodSystems

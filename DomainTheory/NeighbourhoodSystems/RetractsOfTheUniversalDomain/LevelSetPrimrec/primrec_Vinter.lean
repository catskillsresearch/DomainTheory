/-ai
The map sending a paired natural number to the intersection index of its two components
is primitive recursive.

It is the composition of primitive-recursive canonicalization with the
primitive-recursive raw intersection, and the composition agrees with the intersection
index by reflexivity.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.primrec_canonIdx
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.primrec_VinterRaw
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.Vinter

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem primrec_Vinter : Nat.Primrec (fun t => Vinter t.unpair.1 t.unpair.2) :=
  (primrec_canonIdx.comp primrec_VinterRaw).of_eq fun _ => rfl

end DomainTheory.NeighbourhoodSystems

/-ai
Canonicalization of a level-and-mask code is primitive recursive.

The nonemptiness test of the two components is primitive recursive. Selection among that
test, the identity, and the constant code of the pair of zero and one agrees with
canonicalization by reflexivity.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myLevelSetNonempty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.primrec_myLevelSetNonempty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.canonIdx

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.V_no_minimal
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem primrec_canonIdx : Nat.Primrec canonIdx := by
  have hne : Nat.Primrec (fun c => myLevelSetNonempty c.unpair.1 c.unpair.2) :=
    primrec_myLevelSetNonempty
  exact (primrec_selectFn hne primrec_id (Nat.Primrec.const (Nat.pair 0 1))).of_eq fun _ => rfl

end DomainTheory.NeighbourhoodSystems

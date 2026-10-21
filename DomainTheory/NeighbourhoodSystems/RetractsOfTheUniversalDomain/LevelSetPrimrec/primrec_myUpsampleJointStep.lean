/-ai
The joint upsampling step is primitive recursive. It increments the level component of a paired state and replaces the mask by one upsampling step.

The upsampling step on the two components is primitive recursive. Pairing the successor of the left component with that step is primitive recursive, and it agrees with the joint step by reflexivity.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myUpsampleStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.primrec_myUpsampleStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myUpsampleJointStep

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem primrec_myUpsampleJointStep : Nat.Primrec myUpsampleJointStep := by
  have hstep : Nat.Primrec (fun s : ℕ => myUpsampleStep s.unpair.1 s.unpair.2) :=
    primrec_myUpsampleStep
  exact ((Nat.Primrec.succ.comp Nat.Primrec.left).pair hstep).of_eq fun _ => rfl

end DomainTheory.NeighbourhoodSystems

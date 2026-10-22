module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myUpsampleStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.primrec_myUpsampleStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myUpsampleJointStep

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.V_no_minimal
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem primrec_myUpsampleJointStep : Nat.Primrec myUpsampleJointStep := by
  have hstep : Nat.Primrec (fun s : ℕ => myUpsampleStep s.unpair.1 s.unpair.2) :=
    primrec_myUpsampleStep
  exact ((Nat.Primrec.succ.comp Nat.Primrec.left).pair hstep).of_eq fun _ => rfl

end DomainTheory.NeighbourhoodSystems

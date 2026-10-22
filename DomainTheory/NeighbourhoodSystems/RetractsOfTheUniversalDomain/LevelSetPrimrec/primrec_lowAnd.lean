module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.lowAnd

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem primrec_lowAnd : Nat.Primrec (fun t => lowAnd t.unpair.1 t.unpair.2) :=
  (primrec_mul₂ (primrec_mod2.comp Nat.Primrec.left) (primrec_mod2.comp Nat.Primrec.right)).of_eq
    fun _ => rfl

end DomainTheory.NeighbourhoodSystems

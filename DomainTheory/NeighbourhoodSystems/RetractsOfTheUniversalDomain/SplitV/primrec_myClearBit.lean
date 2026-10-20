module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.MinLevel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitV.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive











theorem primrec_myClearBit : Nat.Primrec (fun t => myClearBit t.unpair.1 t.unpair.2) := by
  have hpow : Nat.Primrec (fun t : ℕ => (2 : ℕ) ^ t.unpair.2) := primrec_two_pow Nat.Primrec.right
  exact (primrec_sub₂ Nat.Primrec.left hpow).of_eq fun _ => rfl

end DomainTheory.NeighbourhoodSystems

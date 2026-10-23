module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.MinLevel.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.MinLevel.primrec_minLevel

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive


theorem primrec_minMask : Nat.Primrec (fun t => minMask t.unpair.1 t.unpair.2) := by
  have hm : Nat.Primrec (fun t : ℕ => t.unpair.2) := Nat.Primrec.right
  have hlvl : Nat.Primrec (fun t : ℕ => minLevel t.unpair.1 t.unpair.2) := primrec_minLevel
  have hpow : Nat.Primrec (fun t : ℕ => (2:ℕ) ^ minLevel t.unpair.1 t.unpair.2) :=
    primrec_two_pow hlvl
  exact (primrec.myModPow2.comp (hm.pair hpow)).of_eq fun t => by
    simp only [unpair_pair_fst, unpair_pair_snd, minMask]

end DomainTheory.NeighbourhoodSystems

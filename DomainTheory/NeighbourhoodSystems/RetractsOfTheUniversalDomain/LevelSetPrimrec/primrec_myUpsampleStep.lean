module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myModPow2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.primrec_myModPow2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myUpsampleStep

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem primrec_myUpsampleStep : Nat.Primrec (fun t => myUpsampleStep t.unpair.1 t.unpair.2) := by
  have hs : Nat.Primrec (fun t : ℕ => (2:ℕ) ^ t.unpair.1) := primrec_two_pow Nat.Primrec.left
  have hm' : Nat.Primrec (fun t : ℕ => myModPow2 t.unpair.2 (2 ^ t.unpair.1)) :=
    (primrec_myModPow2.comp (Nat.Primrec.right.pair hs)).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have h2s : Nat.Primrec (fun t : ℕ => (2:ℕ) ^ (2 ^ t.unpair.1)) := primrec_two_pow hs
  exact (primrec_add₂ (primrec_mul₂ h2s hm') hm').of_eq fun t => rfl

end DomainTheory.NeighbourhoodSystems

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.lowAnd
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.primrec_lowAnd
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.landStep

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem primrec_landStep : Nat.Primrec landStep := by
  have hA : Nat.Primrec (fun s : ℕ => s.unpair.1.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.left
  have hB : Nat.Primrec (fun s : ℕ => s.unpair.1.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.left
  have hW : Nat.Primrec (fun s : ℕ => s.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have hAcc : Nat.Primrec (fun s : ℕ => s.unpair.2.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.right
  have hlow : Nat.Primrec (fun s : ℕ => lowAnd s.unpair.1.unpair.1 s.unpair.1.unpair.2) :=
    (primrec_lowAnd.comp (hA.pair hB)).of_eq fun s => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact (((primrec_div2.comp hA).pair (primrec_div2.comp hB)).pair
    ((primrec_mul₂ (Nat.Primrec.const 2) hW).pair
      (primrec_add₂ hAcc (primrec_mul₂ hW hlow)))).of_eq fun _ => rfl

end DomainTheory.NeighbourhoodSystems

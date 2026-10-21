/-ai
The minimal mask of a paired code is primitive recursive.

The right component and the minimal level are primitive recursive, and so is two to the power of that level. Composing the primitive-recursive truncation with their pairing, and unfolding the minimal mask together with the pairing identities, shows that this composition is the minimal mask.
ai-/
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
  exact (primrec_myModPow2.comp (hm.pair hpow)).of_eq fun t => by
    simp only [unpair_pair_fst, unpair_pair_snd, minMask]

end DomainTheory.NeighbourhoodSystems

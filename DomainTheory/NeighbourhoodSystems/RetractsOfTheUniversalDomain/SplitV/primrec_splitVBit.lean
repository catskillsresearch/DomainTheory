/-ai
splitVBit is primitive recursive.

The successor of the minimal level is primitive recursive, hence so is two to that power. The least-set-bit search on the upsampled mask bounded by that power agrees with the splitting bit after the unpair-pair identities.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.MinLevel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitV.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitV.primrec_myFirstBit
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitV.primrec_splitVMinLevel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitV.primrec_splitVUpsampled

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive




















theorem primrec_splitVBit : Nat.Primrec splitVBit := by
  have hk1 : Nat.Primrec (fun n : ℕ => splitVMinLevel n + 1) :=
    Nat.Primrec.succ.comp primrec_splitVMinLevel
  have hbound : Nat.Primrec (fun n : ℕ => (2 : ℕ) ^ (splitVMinLevel n + 1)) :=
    primrec_two_pow hk1
  exact (primrec_myFirstBit.comp (primrec_splitVUpsampled.pair hbound)).of_eq fun n => by
    simp only [unpair_pair_fst, unpair_pair_snd]; rfl

end DomainTheory.NeighbourhoodSystems

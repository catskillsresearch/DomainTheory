/-ai
splitVUpsampled is primitive recursive.

The successor of the minimal level is primitive recursive. Upsampling from the minimal level to that successor on the minimal mask agrees with the upsampled mask after the unpair-pair identities.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.MinLevel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitV.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitV.primrec_splitVMinLevel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitV.primrec_splitVMinMask

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive


theorem primrec_splitVUpsampled : Nat.Primrec splitVUpsampled := by
  have hk1 : Nat.Primrec (fun n : ℕ => splitVMinLevel n + 1) :=
    Nat.Primrec.succ.comp primrec_splitVMinLevel
  exact (primrec_myUpsample.comp
      (primrec_splitVMinLevel.pair (hk1.pair primrec_splitVMinMask))).of_eq fun n => by
    simp only [unpair_pair_fst, unpair_pair_snd]; rfl

end DomainTheory.NeighbourhoodSystems

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.MinLevel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitV.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitV.primrec_myClearBit
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitV.primrec_splitVMinLevel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitV.primrec_splitVUpsampled
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitV.primrec_splitVBit

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive






















theorem primrec_splitVRight : Nat.Primrec splitVRight := by
  have hk1 : Nat.Primrec (fun n : ℕ => splitVMinLevel n + 1) :=
    Nat.Primrec.succ.comp primrec_splitVMinLevel
  have hclear : Nat.Primrec (fun n : ℕ => myClearBit (splitVUpsampled n) (splitVBit n)) :=
    (primrec_myClearBit.comp (primrec_splitVUpsampled.pair primrec_splitVBit)).of_eq fun n => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact (Nat.Primrec.pair hk1 hclear).of_eq fun n => rfl

end DomainTheory.NeighbourhoodSystems

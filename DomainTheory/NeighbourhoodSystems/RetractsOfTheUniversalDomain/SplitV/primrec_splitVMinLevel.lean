/-ai
splitVMinLevel is primitive recursive.

The two components of the canonical index are primitive recursive. The minimal level of that pair agrees with splitVMinLevel after the unpair-pair identities.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.MinLevel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitV.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive















theorem primrec_splitVMinLevel : Nat.Primrec splitVMinLevel := by
  have hk : Nat.Primrec (fun n : ℕ => (canonIdx n).unpair.1) :=
    Nat.Primrec.left.comp primrec_canonIdx
  have hm : Nat.Primrec (fun n : ℕ => (canonIdx n).unpair.2) :=
    Nat.Primrec.right.comp primrec_canonIdx
  exact (primrec_minLevel.comp (hk.pair hm)).of_eq fun n => by
    simp only [unpair_pair_fst, unpair_pair_snd]; rfl

end DomainTheory.NeighbourhoodSystems

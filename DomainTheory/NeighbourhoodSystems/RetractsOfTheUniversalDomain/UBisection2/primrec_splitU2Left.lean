module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.primrec_splitU2MidCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.splitU2Left

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem primrec_splitU2Left : Nat.Primrec splitU2Left :=
  (primrec_clipLtListCode.comp (primrec_splitU2MidCode.pair primrec_canonCode)).of_eq
    fun n => by simp only [splitU2Left, unpair_pair_fst, unpair_pair_snd]

end DomainTheory.NeighbourhoodSystems

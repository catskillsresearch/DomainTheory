module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMinFst
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMaxSnd
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMinFst_le
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMaxSnd_ge

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **`Xₙ`'s intrinsic minimum is strictly below its intrinsic maximum**, via any single
witnessing pair of `canonCode n`'s presenting list (nonempty, `forall_lt_...`). -/
theorem splitU2_min_lt_max (n : ℕ) :
    listMinFst (decodeQPairList (canonCode n)) < listMaxSnd (decodeQPairList (canonCode n)) := by
  obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ (decodeQPairList_canonCode_ne_nil n)
  exact lt_of_le_of_lt (listMinFst_le hp)
    (lt_of_lt_of_le (forall_lt_decodeQPairList_canonCode n p hp) (listMaxSnd_ge hp))

end DomainTheory.NeighbourhoodSystems

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMinFst
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMinFstCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.decodeRat_foldl_ratMin

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem decodeRat_listMinFstCode (c : ℕ) :
    decodeRat (listMinFstCode c) = listMinFst (decodeQPairList c) := by
  unfold listMinFstCode listMinFst decodeQPairList
  rw [foldCode_eq']
  have hstep : (fun (acc x : ℕ) =>
      (fun t : ℕ => ratMinCode (Nat.pair t.unpair.2.unpair.1 t.unpair.1.unpair.1))
        (Nat.pair x (Nat.pair acc 0)))
      = (fun acc x : ℕ => ratMinCode (Nat.pair acc x.unpair.1)) := by
    funext acc x; simp only [unpair_pair_fst, unpair_pair_snd]
  rw [hstep, decodeRat_foldl_ratMin, decodeRat_oneCode]

end DomainTheory.NeighbourhoodSystems

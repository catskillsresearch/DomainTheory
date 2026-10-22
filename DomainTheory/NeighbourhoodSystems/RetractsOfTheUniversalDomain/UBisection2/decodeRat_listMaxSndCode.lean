module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMaxSnd
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMaxSndCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.decodeRat_foldl_ratMax

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem decodeRat_listMaxSndCode (c : ℕ) :
    decodeRat (listMaxSndCode c) = listMaxSnd (decodeQPairList c) := by
  unfold listMaxSndCode listMaxSnd decodeQPairList
  rw [foldCode_eq']
  have hstep : (fun (acc x : ℕ) =>
      (fun t : ℕ => ratMaxCode (Nat.pair t.unpair.2.unpair.1 t.unpair.1.unpair.2))
        (Nat.pair x (Nat.pair acc 0)))
      = (fun acc x : ℕ => ratMaxCode (Nat.pair acc x.unpair.2)) := by
    funext acc x; simp only [unpair_pair_fst, unpair_pair_snd]
  rw [hstep, decodeRat_foldl_ratMax, decodeRat_zeroCode]

end DomainTheory.NeighbourhoodSystems

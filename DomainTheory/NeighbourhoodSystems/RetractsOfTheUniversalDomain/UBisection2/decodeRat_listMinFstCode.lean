/-ai
Decoding the code-level minimum of first components equals the list-level minimum of first components of the decoded pair list.

Unfold both minima and the decoded list. Rewrite by the code-fold equation. The code-level step, after the state is paired, agrees with the rational minimum of the accumulator and the first component, by simplifying the unpairing of a pair. Rewrite by that agreement, the decoding bridge for the minimum fold, and decoding of the one code.
ai-/
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

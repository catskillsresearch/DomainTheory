/-ai
Decoding the left fold, along a list, of the step that pairs the current entry on the left with a fixed parameter and then applies the pair-map step to the accumulator, equals the reverse of that list with each entry paired on the left with the parameter, appended to the decoding of the starting accumulator.

The proof is by induction on the list, generalizing the accumulator. The empty list simplifies. For a cons cell, rewrite the fold, apply the inductive hypothesis, and rewrite by the pair-step equation, the decoding of one pair step, and the cons, reverse, and append identities.
ai-/
module

public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Data.Nat.Pairing
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.List.Basic
public import Mathlib.Computability.Partrec
public import Mathlib.Tactic.Ring
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.mapPairStp_eq
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.decodeList_mapPairStep

@[expose] public section


namespace Domain.Recursive


theorem decodeList_foldl_mapPairStp (n : ℕ) (el : List ℕ) (acc : ℕ) :
    decodeList (List.foldl (fun acc x => mapPairStp (Nat.pair x (Nat.pair acc n))) acc el)
      = (el.map (Nat.pair n ·)).reverse ++ decodeList acc := by
  induction el generalizing acc with
  | nil => simp
  | cons e el ih =>
    rw [List.foldl_cons, ih, mapPairStp_eq, decodeList_mapPairStep, List.map_cons,
      List.reverse_cons, List.append_assoc, List.singleton_append]

end Domain.Recursive

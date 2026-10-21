/-ai
Decoding the left fold that takes rational maxima of an accumulator with the second components of a list of codes equals the left fold of the maximum of the second components of the decoded pairs, started at the decoded seed.

Induct on the list, generalizing the seed. The empty list is reflexive. For a cons cell, rewrite both folds and the mapped list by the cons equations, apply the inductive hypothesis, and rewrite by decoding of the rational maximum.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem decodeRat_foldl_ratMax (l : List ℕ) (z : ℕ) :
    decodeRat (l.foldl (fun acc x => ratMaxCode (Nat.pair acc x.unpair.2)) z)
      = (l.map decodeRatPair).foldl (fun acc p => max acc p.2) (decodeRat z) := by
  induction l generalizing z with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldl_cons, List.map_cons, List.foldl_cons, ih, decodeRat_ratMaxCode]
    rfl

end DomainTheory.NeighbourhoodSystems

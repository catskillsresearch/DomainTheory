/-ai
Decoding the left fold that takes rational minima of an accumulator with the first components of a list of codes equals the left fold of the minimum of the first components of the decoded pairs, started at the decoded seed.

Induct on the list, generalizing the seed. The empty list is reflexive. For a cons cell, rewrite both folds and the mapped list by the cons equations, apply the inductive hypothesis, and rewrite by decoding of the rational minimum.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- Bridging `List.foldl` over raw pair-codes (via `ratMinCode`) to `List.foldl` over decoded
pairs (via `min ·.1`), one step at a time. -/
theorem decodeRat_foldl_ratMin (l : List ℕ) (z : ℕ) :
    decodeRat (l.foldl (fun acc x => ratMinCode (Nat.pair acc x.unpair.1)) z)
      = (l.map decodeRatPair).foldl (fun acc p => min acc p.1) (decodeRat z) := by
  induction l generalizing z with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldl_cons, List.map_cons, List.foldl_cons, ih, decodeRat_ratMinCode]
    rfl

end DomainTheory.NeighbourhoodSystems

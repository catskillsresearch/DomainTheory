/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Exercise812d
public import DomainTheory.Neighborhood.Exercise812e.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open Domain.Recursive


namespace ComputableBisection

variable {α γ : Type*} {V : NeighborhoodSystem α} {W : NeighborhoodSystem γ}
  (P : ComputablePresentation V) (hDiff : IsComputableDiff P)
  {Q : ComputablePresentation W} (B : ComputableBisection Q) (hWnomin : W.NoMinimal)




section Congr

variable {n n' k k' m m' : ℕ}



/-- **`negIdxFromBisection` is a well-defined function of sets**, the same argument as
`posIdxFromBisection_congr` with `B.right_congr` in place of `B.left_congr`. -/
theorem negIdxFromBisection_congr (hpos : V.IsPositive) (hnomin : V.NoMinimal)
    (hdiffClosed : V.DiffClosed) (hn : P.X n = P.X n') (hk : P.X k = P.X k')
    (hm : Q.X m = Q.X m') :
    Q.X (negIdxFromBisection P hDiff B n m k) = Q.X (negIdxFromBisection P hDiff B n' m' k') := by
  unfold negIdxFromBisection
  rw [emptyInterDec_congr P hpos hnomin hn hk, emptyDiffDec_congr P hDiff hdiffClosed hnomin hn hk]
  have hle1 := emptyInterDec_le_one P (Nat.pair n' k')
  have hle2 := emptyDiffDec_le_one P hDiff (Nat.pair n' k')
  have h1 : emptyInterDec P (Nat.pair n' k') = 0 ∨ emptyInterDec P (Nat.pair n' k') = 1 := by omega
  have h2 : emptyDiffDec P hDiff (Nat.pair n' k') = 0 ∨
      emptyDiffDec P hDiff (Nat.pair n' k') = 1 := by omega
  rcases h1 with h1 | h1
  · simp only [h1, selectFn_zero]
    rcases h2 with h2 | h2
    · simp only [h2, selectFn_zero]; exact B.right_congr m m' hm
    · simp only [h2, selectFn_one]; exact hm
  · simp only [h1, selectFn_one]; exact hm

end Congr
end ComputableBisection
end DomainTheory.Neighborhood

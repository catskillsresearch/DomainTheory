/-ai
This file gathers and re-exports the presentation-independent canonical bisection of the universal domain: the minimum of first components and the maximum of second components of a presenting list, their code-level folds, the midpoint code and the left and right splits, the bounds, attainment, tightness, lower and upper estimates, and congruence lemmas, the decoding bridges and primitive recursiveness, the neighbourhood identities, disjointness, union, and congruence of the splits, and the packaged computable bisection.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMinFst
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMaxSnd
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMinFstCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMaxSndCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.splitU2MidCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.splitU2Left
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.splitU2Right
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.UBisection2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.forall_bounds_decodeQPairList_canonCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.foldl_minFst_le_seed
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.foldl_minFst_le
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.foldl_minFst_mem_or_eq_seed
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.foldl_maxSnd_seed_le
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.foldl_maxSnd_ge
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.foldl_maxSnd_mem_or_eq_seed
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMinFst_le
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMaxSnd_ge
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMinFst_attained
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMaxSnd_attained
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMinFst_mem_presentedIntervals
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMinFst_lower_bound
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMaxSnd_upper_bound
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMaxSnd_tight
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMinFst_congr
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMaxSnd_congr
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.primrec_listMinFstCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.primrec_listMaxSndCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.decodeRat_foldl_ratMin
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.decodeRat_foldl_ratMax
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.decodeRat_listMinFstCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.decodeRat_listMaxSndCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.primrec_splitU2MidCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.primrec_splitU2Left
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.primrec_splitU2Right
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.decodeRat_splitU2MidCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.splitU2_min_lt_max
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.splitU2_min_lt_mid
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.splitU2_mid_lt_max
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.UX_splitU2Left
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.UX_splitU2Right
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.splitU2_disjoint
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.splitU2_union
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.splitU2MidCode_congr
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.splitU2Left_congr
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.splitU2Right_congr

@[expose] public section

/-!
# Exercise 8.12(f), prerequisite — a *presentation-independent* canonical bisection of `U`

`SplitU.lean`'s `splitULeft`/`splitURight` (built for Theorem 8.8(b)) split `Xₙ` at the midpoint of
`canonCode n`'s **first presenting pair** — but `canonCode` only clips/filters, it never *merges*
overlapping or adjacent intervals, so two different (both already-canonical, in the sense of
`canonList_fixed`) presenting lists of the *same* `U`-neighbourhood can have different first pairs
(e.g. `[(0,1)]` vs. `[(0, 1/2), (1/2, 1)]` both present `U.master`, but their first pairs' midpoints
are `1/2` and `1/4`). So `splitULeft`/`splitURight` do **not** satisfy `ComputableBisection`'s
`left_congr`/`right_congr` — this is a genuine gap in reusing `SplitU.lean` "as is" for `8.12(f)`,
mirroring the gap `MinLevel.lean` fixed for `V`'s side of `8.12(e)(d)`.

## The fix: split at the midpoint of `(min, max)` instead of the first pair

Rather than building full interval-merging machinery (as `MinLevel.lean` effectively had to for
`V`'s levels), a much lighter invariant suffices here: for a finite union of half-open rational
intervals `X = ⋃ Ico pᵢ.1 pᵢ.2`,

* `min X = min_i pᵢ.1` (attained — every `Ico` is left-closed, and every point of the union is `≥`
  some `pᵢ.1 ≥ min_i pᵢ.1`), and
* `sup X = max_i pᵢ.2` (not necessarily attained, but this is *still* a fact purely about the set
  `X`, not about which particular representing list computes it — `sup` of a finite union is the
  `max` of the individual `sup`s, and each `Ico pᵢ.1 pᵢ.2` has `sup = pᵢ.2`).

Both quantities are therefore genuinely **intrinsic to the set** `X`, not to the specific
presenting list — so splitting at their midpoint is automatically presentation-independent, with no
need to ever canonicalize/merge/sort the interval list itself. `listMinFst`/`listMaxSnd` below
compute exactly these two quantities as primitive-recursive folds over `canonCode n`'s list, reusing
`SplitU.lean`'s `clipLtListCode`/`clipGeListCode` unchanged for the actual clipping.
-/

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-! ### Every pair of `canonCode c`'s list lies in `[0, 1]` -/


/-! ### `listMinFst`/`listMaxSnd`: the two intrinsic quantities, at the `List (ℚ × ℚ)` level -/



















/-! ### `listMinFst`/`listMaxSnd`, at the code level (`listMinFstCode`/`listMaxSndCode`)

Fold `ratMinCode`/`ratMaxCode` over the raw pair-code list via `Recursive.lean`'s `foldCode`,
mirroring `listMinFst`/`listMaxSnd`'s list-level folds exactly (seed `oneCode`/`zeroCode`, no
`params` needed). -/









/-! ### `splitU2`: the presentation-independent midpoint split -/







/-! ### Correctness -/












end DomainTheory.NeighbourhoodSystems

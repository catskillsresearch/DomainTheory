/-ai
This file gathers and re-exports the definitions for the explicit deterministic split of a U-neighbourhood in Theorem 8.8(b), Part 4: the one-sided clips of a rational pair, their codes and list codes, the code of the first list element, the midpoint code of the first pair of the canonical presentation, and the left and right halves of the split.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.qpClipLt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.qpClipGe
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.clipLtCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.clipGeCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.clipLtListCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.clipGeListCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.firstElemCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.splitMidCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.splitULeft
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.splitURight

@[expose] public section

/-!
# Theorem 8.8(b), Part 4 — an explicit, deterministic `splitU`

`Definition87.lean`'s `U_no_minimal` shows every `U`-neighbourhood splits into two proper disjoint
`U`-neighbourhoods, but only as a bare existential (`∃ Y Z, ...`), built via `Classical`-flavoured
case analysis on an arbitrary witness of non-emptiness. Theorem 8.8(b)'s eventual `Y_n` chain
(Part 6) needs to *compute* such a split from an index `n` alone — so here we replace the
existential by a genuinely `Nat.Primrec` pair `splitULeft`/`splitURight : ℕ → ℕ`, and reprove
`U_no_minimal`'s four properties (disjoint, covering, both proper) for this canonical choice.

## The construction

Given an index `n`, canonicalize it (`canonCode n`, Part 3) to get a genuine presenting list, all
of whose pairs are already non-degenerate (`forall_lt_decodeQPairList_canonCode`). Take its
**first** pair `p₀ = decodeRatPair (firstElemCode (canonCode n))` (no search needed — the *first*
pair always works, unlike `U_no_minimal`'s arbitrary witness of non-emptiness) and split at its
rational midpoint `m := (p₀.1 + p₀.2)/2` (`ratMidCode`, computed with no genuine division — see
`RationalPrimrec.lean`): `splitULeft n` re-clips every pair of `canonCode n` into `(-∞, m)`
(`clipLtListCode`), `splitURight n` into `[m, ∞)` (`clipGeListCode`). Both are realized at the code
level via `RecursiveCross.lean`'s `flatMapCode`, threading `m` through as the fixed parameter.

Correctness (`UX_splitULeft`/`UX_splitURight`) shows these compute exactly `Xₙ ∩ (-∞,m)` /
`Xₙ ∩ [m,∞)` as *sets*, mirroring `U_no_minimal`'s own proof almost verbatim; `splitU_disjoint`/
`splitU_union`/`splitU_left_ne`/`splitU_right_ne` package the four properties.
-/

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-! ### Public one-sided clips (`Definition87.lean`'s `clipLt`/`clipGe` are `private`) -/


/-! ### One-sided clips, at the code level -/


/-! ### Mapping a one-sided clip over a whole list, at the code level

`flatMapCode f x c` codes `(decodeList c).flatMap (fun y => decodeList (f (pair x y)))`, with `x`
threaded through as a *fixed* parameter — exactly what's needed here, with `x := m` the (already
computed) midpoint code and `f := fun t => [clip t]` (singleton). -/


/-! ### The first pair of a non-empty list code -/


/-! ### `splitU`: the canonical midpoint split -/


/-! ### Correctness -/
end DomainTheory.NeighbourhoodSystems

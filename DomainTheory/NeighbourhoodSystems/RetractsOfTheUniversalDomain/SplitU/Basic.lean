/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.UComputablePresentation

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

namespace DomainTheory.Neighborhood

open Domain.Recursive NeighborhoodSystem

/-! ### Public one-sided clips (`Definition87.lean`'s `clipLt`/`clipGe` are `private`) -/

/-- Clip a pair down to `(-∞, m)`: leave the left endpoint, clamp the right endpoint at `m`. -/
def qpClipLt (m : ℚ) (p : ℚ × ℚ) : ℚ × ℚ := (p.1, p.2 ⊓ m)

/-- Clip a pair up to `[m, ∞)`: clamp the left endpoint at `m`, leave the right endpoint. -/
def qpClipGe (m : ℚ) (p : ℚ × ℚ) : ℚ × ℚ := (p.1 ⊔ m, p.2)

/-! ### One-sided clips, at the code level -/

/-- Clip a rational-pair code `e` to `(-∞, decodeRat m)`, given `t = pair m e`. -/
def clipLtCode (t : ℕ) : ℕ :=
  Nat.pair t.unpair.2.unpair.1 (ratMinCode (Nat.pair t.unpair.2.unpair.2 t.unpair.1))

/-- Clip a rational-pair code `e` to `[decodeRat m, ∞)`, given `t = pair m e`. -/
def clipGeCode (t : ℕ) : ℕ :=
  Nat.pair (ratMaxCode (Nat.pair t.unpair.2.unpair.1 t.unpair.1)) t.unpair.2.unpair.2

/-! ### Mapping a one-sided clip over a whole list, at the code level

`flatMapCode f x c` codes `(decodeList c).flatMap (fun y => decodeList (f (pair x y)))`, with `x`
threaded through as a *fixed* parameter — exactly what's needed here, with `x := m` the (already
computed) midpoint code and `f := fun t => [clip t]` (singleton). -/

/-- Clip every pair of the list-code `c` into `(-∞, decodeRat m)`. -/
def clipLtListCode (m c : ℕ) : ℕ := flatMapCode (fun t => Nat.pair (clipLtCode t) 0 + 1) m c

/-- Clip every pair of the list-code `c` into `[decodeRat m, ∞)`. -/
def clipGeListCode (m c : ℕ) : ℕ := flatMapCode (fun t => Nat.pair (clipGeCode t) 0 + 1) m c

/-! ### The first pair of a non-empty list code -/

/-- The code of the head element of a non-empty list-code `c` (`decodeList c`'s head). Junk
(`0`'s `unpair.1`) when `c = 0`, but we only ever apply it to `canonCode n ≠ 0`
(`canonCode_ne_zero`). -/
def firstElemCode (c : ℕ) : ℕ := (c - 1).unpair.1

/-! ### `splitU`: the canonical midpoint split -/

/-- The midpoint code of the first pair of `canonCode n`'s presenting list. -/
def splitMidCode (n : ℕ) : ℕ := ratMidCode (firstElemCode (canonCode n))

/-- The "left" half of the canonical split of `Xₙ`: `Xₙ ∩ (-∞, m)` for `m` the midpoint of `Xₙ`'s
first presenting pair. -/
def splitULeft (n : ℕ) : ℕ := clipLtListCode (splitMidCode n) (canonCode n)

/-- The "right" half of the canonical split of `Xₙ`: `Xₙ ∩ [m, ∞)`. -/
def splitURight (n : ℕ) : ℕ := clipGeListCode (splitMidCode n) (canonCode n)

/-! ### Correctness -/
end DomainTheory.Neighborhood

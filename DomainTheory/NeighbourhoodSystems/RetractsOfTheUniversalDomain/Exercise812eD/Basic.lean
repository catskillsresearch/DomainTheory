/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitV
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812eD.Udiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812eD.U_isComputableDiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812eD.B812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812eD.splitX812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812eD.isComputableSplit_812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812eD.Udiff_primrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812eD.Udiff_eq_diff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812eD.U_diff_iff_nonempty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812eD.Udiff_spec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812eD.U_diff_computable

@[expose] public section

/-!
# Exercise 8.12(e)(d)(iii) (Scott 1981, PRG-19, Lecture VIII) — package as `ComputableBisection`;
instantiate for `U` ↔ `V`

The exercise's literal target, given `(e)(d)(i)`–`(ii)`: a concrete `splitX812e : Set ℚ → Set ℕ →
Set ℚ → Set ℕ × Set ℕ` satisfying `IsComputableSplit UComputablePresentation
VComputablePresentation splitX812e`.

## A gap found while assembling this (not present in the earlier scoping): `U`'s missing
`IsComputableDiff` witness

`(e)(d)`'s own `arxiv.md` draft signature — `splitFromBisection UComputablePresentation (U's
`IsComputableDiff`) B812e` — assumed an `IsComputableDiff UComputablePresentation` instance already
existed somewhere in the codebase. It does not: grep-confirmed, `IsComputableDiff` (`Exercise812d.lean`,
`(d)(3)(a)`) has never been instantiated for either `U` or `V`. Building it is, however, genuinely
mechanical — not a new mathematical gap like `(e)(d)(i)`/`(ii)`'s — since `IntervalPrimrec.lean`
already supplies **every** raw piece unconditionally: `diffCode`/`primrec_diffCode` (the code-level
set-difference primitive) and `presentedIntervals_decodeQPairList_diffCode` (its correctness,
unconditional — no case split on emptiness needed, unlike `combineCode`'s consistency side of the
story). `Udiff`/`Udiff_primrec`/`Udiff_spec`/`U_diff_computable` below are a direct structural mirror
of `UComputablePresentation.lean`'s own `Uinter`/`Uinter_primrec`/`Uinter_spec`/`U_cons_computable`,
substituting `diffCode` for `combineCode` and `U_diff_mem` (`Exercise812c.lean`, already `Pass`) for
`U`'s `IsPositive` as the "always mem-or-∅" fact driving the decidability reduction.
-/

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-! ## `U_isComputableDiff` -/








/-! ## `B812e`, `splitX812e`, `isComputableSplit_812e` — the exercise's literal target

Mechanical given `(e)(d)(i)`–`(ii)` and `U_isComputableDiff` above: `B812e` is a direct
field-by-field assembly from `SplitV.lean`'s already-`Pass` declarations; `splitX812e`/
`isComputableSplit_812e` are one-line instantiations of `Exercise812e.lean`'s generic
`splitFromBisection`/`isComputableSplit_ofBisection`, fed `U`'s already-`Pass`
`IsPositive`/`NoMinimal`/`DiffClosed` facts (`Exercise812c.lean`). -/



end DomainTheory.NeighbourhoodSystems

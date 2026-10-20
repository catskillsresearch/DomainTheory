/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myDivPow2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myModPow2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myTestBit
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.lowAnd
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.landStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myLand
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myUpsampleStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myUpsampleJointStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myUpsample
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.levelSetNonemptyBody
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myLevelSetNonempty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.canonIdx
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.VX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.VinterRaw
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.Vinter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.VmasterIdx
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.VComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.primrec_myDivPow2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myDivPow2_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.primrec_myModPow2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myModPow2_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myModPow2_lt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.primrec_myTestBit
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myTestBit_eq_one_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.primrec_lowAnd
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.lowAnd_eq_mod
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.primrec_landStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.primrec_myLand
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.land_low_rec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.landStep_iter_spec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myLand_eq_land
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.primrec_myUpsampleStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.mod_eq_sub_of_le_of_lt_two_mul
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.levelSet_myUpsampleStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.primrec_myUpsampleJointStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myUpsampleJointStep_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myUpsampleJointStep_iter_level
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myUpsampleJointStep_iter_levelSet
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.levelSet_myModPow2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.primrec_myUpsample
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.levelSet_myUpsample
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myUpsample_lt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.primrec_levelSetNonemptyBody
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.primrec_myLevelSetNonempty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myLevelSetNonempty_le_one
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myLevelSetNonempty_eq_one_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.levelSet_inj_of_lt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.primrec_canonIdx
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.canonIdx_eq_self_of_nonempty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.canonIdx_eq_master_of_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.levelSet_canonIdx_nonempty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.canonIdx_idempotent
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.VX_canonIdx
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.V_mem_VX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.VX_nonempty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.V_surj_VX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.levelSet_myInter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.levelSet_eq_iff_myUpsample_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.primrec_VinterRaw
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.levelSet_VinterRaw
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.Vcons_iff_nonempty_inter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.V_interEq_computable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.V_cons_computable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.primrec_Vinter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.Vinter_spec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.VX_VmasterIdx

@[expose] public section

/-!
# Exercise 8.12(b) (Scott 1981, PRG-19, Lecture VIII) — `V`'s computable presentation

Builds the `Nat.Primrec` bit-manipulation infrastructure `Exercise812.lean`'s docstring flagged as
missing ("upsample a bitmask from level `k` to level `k'`, computably"), and assembles it into a
genuine `ComputablePresentation V`, closing Exercise 8.12(b).

## Design

Mirrors `UComputablePresentation.lean`'s two-layer shape (canonicalize an arbitrary code, then wire
Scott's two relations) combined with `Example78.lean`'s choice-free bit-level idiom (`myLor`, built
by hand since mathlib's `Nat.lor`/`Nat.testBit` are not exposed as `Nat.Primrec`):

* **Bit extraction** (`myDivPow2`/`myTestBit`): `Nat.Primrec` versions of `n ↦ n / 2^ℓ` and
  `n ↦ n.testBit ℓ`, built by iterating "halve" `ℓ` times via `Nat.Primrec.prec` (the same
  "iterate a step a data-dependent number of times" idiom `primrec_foldCode`/`myLor` already use).
* **`myLand`** (bitwise AND): a hand-built choice-free primitive-recursive `&&&`, mirroring `myLor`
  bit-for-bit (literally: `lowOr`/`lorStep` become `lowAnd`/`landStep`, `Nat.testBit_lor` becomes
  `Nat.testBit_and`).
* **`myUpsample`** (the missing piece): re-expressing a level-`k` bitmask at level `k' ≥ k`. The key
  realization is that `Exercise812.lean`'s `upsample`'s one-level step is *arithmetic*, not
  bit-by-bit: doubling `m` from level `k` to `k+1` duplicates its low `2^k` bits into a second copy
  shifted up by `2^k` positions, i.e. `m' + m' * 2 ^ (2 ^ k)` where `m' := m % 2 ^ (2 ^ k)` is `m`'s
  low `2^k`-bit truncation (`myModPow2`, itself built from `myDivPow2`). Truncating first avoids any
  addition-carry ambiguity from `m`'s "junk" bits at positions `≥ 2^k` (irrelevant to `levelSet k m`
  as a *set*, but would corrupt a naive `m + m * 2^(2^k)`). Iterating this step `k' - k` times (again
  via `Nat.Primrec.prec`, jointly tracking the current level alongside the mask, exactly as `lorStep`
  jointly tracks two running arguments) gives `myUpsample`.
* **Nonemptiness** (`myLevelSetNonempty`): `(levelSet k m).Nonempty ↔ ∃ ℓ < 2^k, m.testBit ℓ`
  (`levelSet_nonempty_iff`) is a bounded `∃` of a decidable predicate, handled by the existing
  `bExistsFn` combinator with `myTestBit` as the body — no new quantifier infrastructure needed.
* **Canonicalization** (`canonIdx`/`VX`): exactly `UComputablePresentation.lean`'s `canonCode`
  pattern, but simpler (no "clip to `[0,1)`" step is needed — a `(k, m)` pair is always a
  *syntactically* well-formed level/mask pair, only possibly empty): keep a code `n = pair k m`
  unchanged if `levelSet k m` is non-empty, else fall back to the fixed master code `pair 0 1`
  (`levelSet 0 1 = univ`, `levelSet_zero_one`).
* **Scott's two relations reduce to bitmask arithmetic**: `Vinter n m`'s raw intersection is
  `myUpsample`-both-then-`myLand` at the joint level `max k₁ k₂` (mirroring `levelSet_inter`
  exactly), and consistency reduces to that merged mask being non-empty (`myLevelSetNonempty`);
  equality of two canonicalized codes' `levelSet`s reduces to equality of their masks *after*
  upsampling both to a common level (`levelSet` is injective in the mask at any fixed level,
  `levelSet_inj_of_common_level`), decided by `RecDecidable.natEq`.

Everything here is choice-free by construction (`Nat.Primrec` terms built from the seven base
combinators plus already-choice-free helpers); the correctness *lemmas* connecting these to
`Exercise812.lean`'s `Set`-level `levelSet`/`upsample` go through ordinary `Nat` arithmetic
(`Nat.testBit_eq_decide_div_mod_eq`, `Nat.testBit_and`, `Nat.div_add_mod`, …), which — like every
other file in this project touching `ℕ`'s order/decidability API — reports the same inherited
`Classical.choice` footprint documented in `Definition87.lean`/`Exercise812.lean`, not a new choice
introduced here.
-/

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-! ### Bit extraction: `myDivPow2`, `myModPow2`, `myTestBit` -/











/-! ### Choice-free primitive-recursive bitwise AND (`myLand`)

Mirrors `myLor` (`Recursive.lean`) bit-for-bit, swapping `Nat.testBit_lor`/`lowOr` for
`Nat.testBit_and`/`lowAnd`. Needed because `levelSet_inter`'s formula combines two upsampled masks
with `&&&`, and mathlib's `Nat.land` is (like `Nat.lor`) not itself exposed as `Nat.Primrec`. -/











/-! ### `myUpsample`: a computable version of `Exercise812.lean`'s `upsample`

The one-level step is *arithmetic*: `myUpsampleStep k m := 2 ^ (2 ^ k) * m' + m'` where
`m' := myModPow2 m (2 ^ k)` is `m`'s low-`2^k`-bit truncation. Truncating first is what makes the
formula correct regardless of any "junk" bits `m` may carry at positions `≥ 2^k` (irrelevant to
`levelSet k m` as a set, but would corrupt a naive `m + m * 2^(2^k)`): mathlib's
`Nat.testBit_two_pow_mul_add` handles exactly the "low/high digit" splitting this needs, given the
truncation bound `myModPow2_lt`. -/















/-! ### Non-emptiness of `levelSet k m` is recursively decidable

`levelSet_nonempty_iff` phrases `(levelSet k m).Nonempty` as a bounded `∃ ℓ < 2 ^ k, m.testBit ℓ`;
this is exactly what the existing `bExistsFn` combinator (`Recursive.lean`) decides, with
`myTestBit` supplying the (already primitive-recursive) body. -/







/-! ### `levelSet k _` is injective on bounded masks

Needed to decide *equality* of two `levelSet`s from their bitmask codes: two bounded masks
(`< 2 ^ (2 ^ k)`, i.e. with no "junk" bits at positions `≥ 2^k`) presenting the same `levelSet k _`
must already be the same natural number. Combined with `myUpsample_lt` (which guarantees
boundedness unconditionally), this reduces `levelSet`-equality-after-upsampling to plain `ℕ`
equality of the upsampled codes. -/


/-! ### Canonicalizing an arbitrary `(level, mask)` code

Mirrors `UComputablePresentation.lean`'s `canonCode`, but simpler: a `(k, m)` pair is always a
syntactically well-formed `levelSet` presentation, only possibly *empty* — no "clip to `[0,1)`"
pass is needed, just the non-emptiness check `myLevelSetNonempty` already built. -/







/-! ### `V`'s enumeration `VX` -/






/-! ### Scott's two relations for `V`

`levelSet_inter` (`Exercise812.lean`) says the *raw* intersection of two `levelSet`s is again a
`levelSet`, unconditionally — mirroring `Example78.lean`'s `PN` rather than `Definition87.lean`'s
`U`. We re-derive it computably: bridge `levelSet_inter_same_level`'s same-level `&&&`-formula
through `myUpsample`/`myLand`. -/














end DomainTheory.NeighbourhoodSystems

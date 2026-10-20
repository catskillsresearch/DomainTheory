/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem76

@[expose] public section

/-!
# Theorem 8.6(c) (Scott 1981, PRG-19, Lecture VIII) — `sub` is computable

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19, Theorem 8.6's
third clause: *"If `E` is effectively given, then `sub` is computable."* Here "`sub`" means the
combinator packaged as an approximable map on the function space (`Sub8_6.subApprox : ApproximableMap
(funSpace E E) (funSpace E E)`, Theorem 8.6(b)(i)), and "computable" is relative to the
function-space presentation that Theorem 7.5 builds out of any presentation of `E`.

## Strategy (choice-free), mirroring Theorem 7.6's `fixMap_isComputable`

`subApprox` was built via Exercise 2.13's `ofContinuous`, so its neighbourhood relation unfolds
(via `ofMono`) to: `subApprox.rel F G ↔ ∃ hF : (funSpace E E).mem F, sub (toApproxMap (↑F)).mem
G`-ish, i.e. (using `toFilter`'s definition) `F subApprox G` holds iff `sub` of `F`'s least map lies
*in* `G` as a literal set of approximable maps (`subApprox_rel_iff`). Specializing `F = Xenum n`,
`G = Xenum m` (Theorem 7.5's enumeration) and unfolding membership via `mem_Xenum_iff_map`:

`(Xenum n) subApprox (Xenum m)` iff, for every coded step `⟨X_{e.1}, X_{e.2}⟩` of (consistent)
`Xenum m`, `sub(ĝₙ)` relates `X_{e.1}` to `X_{e.2}`, where `ĝₙ = toApproxMap(↑(Xenum n))` is
`Xenum n`'s least map (Theorem 7.6's `leastMap_Xenum_rel`).

`sub`'s own formula (`sub_rel`) turns this into an *existential* over a witness neighbourhood `Y`
with `ĝₙ.rel Y Y`; `P.surj` lets `Y` range over presentation indices `y`, and — crucially —
`ĝₙ.rel (X_y) (X_y) ↔ Xenum n ⊆ Xenum (codePair y y)` (Theorem 7.6) is **recursively decidable** via
the function-space presentation's own `incl_computable`. So the whole relation is a *finite*
conjunction (bounded `∀` over the coded list `decodeList m`, guarded by the decidable consistency
flag `gN m = 1`) of an *unbounded* existential (`∃ y`) of a decidable predicate — hence
recursively enumerable, exactly like Theorem 7.6's `fix`. Unlike `fix`, there is no need for a
*chain*: a single witness index `y` suffices (Scott's formula for `sub` has one existential, not an
iterated fixed-point search), so this file is comparably shorter than `Theorem76.lean`.

Everything here is **choice-free** (`⊆ {propext, Quot.sound}`): the search predicate and its
decidability are all built from `RecDecidable`/`REPred` closure lemmas over concrete primitive
recursive characteristic functions, exactly as in `Theorem75.lean`/`Theorem76.lean`.
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Sub8_6

variable {α : Type*} {E : NeighborhoodSystem α}

/-! ### Unfolding `subApprox`'s neighbourhood relation -/

section SubComputable

variable (P : ComputablePresentation E) (gN : ℕ → ℕ)
  (hgN : ∀ c, gN c = 1 ↔
    (stepFun (funListOf P P (decodeList c)) : Set (ApproximableMap E E)).Nonempty)

/-! ### The per-witness decidable predicate and its recursive decidability -/
end SubComputable
end DomainTheory.NeighbourhoodSystems

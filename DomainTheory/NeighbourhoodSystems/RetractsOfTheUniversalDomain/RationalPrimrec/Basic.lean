/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.decodeInt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.encodeInt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.decodeRat
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.encodeRat
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.qNumP
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.qNumN
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.qDen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.ratLeCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.ratLtCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.ratMaxCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.ratMinCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.zeroCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.oneCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.ratMidCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.decodeInt_encodeInt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.decodeRat_encodeRat
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.decodeRat_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.decodeRat_zeroCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.decodeRat_oneCode

@[expose] public section

/-!
# A choice-free Gödel numbering of `ℚ`, with primitive-recursive comparison/max/min

Theorem 8.8(b) (Scott 1981, PRG-19) needs `𝒰` (Definition 8.7) to have a genuine
`ComputablePresentation` (Definition 7.1). `𝒰`'s neighbourhoods are finite unions of rational
intervals `presentedIntervals L` for `L : List (ℚ × ℚ)`, so we first need `ℚ` itself — and hence
`List (ℚ × ℚ)` — coded by naturals, with the *arithmetic* operations `combineIntervals` actually
performs (`⊔`, `⊓`, `≤`, `=`) realized as genuinely `Nat.Primrec` functions on the codes.

## The encoding

An integer `z : ℤ` is coded as an (unnormalized) **difference pair** `Nat.pair z.toNat (-z).toNat`
— deliberately *not* a zig-zag bijection, since a difference pair turns every integer comparison
into a cross-*addition* of naturals (`a₁ - b₁ ≤ a₂ - b₂ ↔ a₁ + b₂ ≤ a₂ + b₁`), avoiding truncated
subtraction (and its case splits) entirely in the downstream `Nat.Primrec` proofs. A rational
`q : ℚ` is coded as `Nat.pair (encodeInt q.num) (q.den - 1)` (the `- 1`/`+ 1` shift keeps the
denominator positive without a separate side condition). Both round-trip **exactly** on every input
(`decodeInt_encodeInt`, `decodeRat_encodeRat`), not just on some "canonical" sub-class of codes —
mirroring `Recursive.lean`'s `decodeList_encodeList`/`encodeList_decodeList` exact round trips, and
for the same reason: it lets downstream code freely compose `encode ∘ decode` without tracking a
canonicality invariant.

`decodeRat`'s surjectivity (`decodeRat_surjective`) is what lets `𝒰`'s presentation enumerate *every*
rational, and `mkRat_self` (core Lean, choice-free) is the only fact about `Rat`'s internal
normalization we need.

## Primitive-recursive comparison arithmetic

`ratLeCode`/`ratLtCode`/`ratEqCode` decide `≤`/`</`/`=` between two rational codes by cross-clearing
denominators (again via addition, not subtraction, exactly as for `Int`); `ratMaxCode`/`ratMinCode`
select one of the two input codes via `Domain.Recursive.selectFn`, mirroring
`Domain.Recursive.primrec_max`'s pattern exactly. `zeroCode`/`oneCode` are fixed codes for the
constants `0, 1 : ℚ` used by `Definition87.lean`'s `clip`.

Everything here is `⊆ {propext, Quot.sound}` — no `Classical.choice` — since it is all direct
`Nat.Primrec` construction and finite case-splitting on `≤`/`<` (decidable, not classical, for `ℤ`
and `ℚ`).
-/

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

/-! ### Integers as difference-pairs of naturals -/




/-! ### Rationals as (integer numerator code, denominator `- 1`) pairs -/




/-! ### Primitive-recursive comparison of rational codes

`ratLeCode (pair c₁ c₂)` decides `decodeRat c₁ ≤ decodeRat c₂` by cross-clearing denominators:
writing `cᵢ` for `(aᵢ, bᵢ, dᵢ)` (so `decodeRat cᵢ = (aᵢ - bᵢ)/(dᵢ + 1)`), the comparison
`(a₁-b₁)/(d₁+1) ≤ (a₂-b₂)/(d₂+1)` (denominators positive) is equivalent, after moving every `bᵢ`
term to the other side to avoid subtraction, to `a₁(d₂+1) + b₂(d₁+1) ≤ a₂(d₁+1) + b₁(d₂+1)`. -/







/-! ### Max/min of rational codes, and constants -/







/-! ### The midpoint of two rational codes (needed for Theorem 8.8(b) Part 4's `splitU`)

`ratMidCode (pair c₁ c₂)` codes `(decodeRat c₁ + decodeRat c₂) / 2` **without performing any
division**: cross-clearing denominators as in `ratLeCode` turns the sum into a single fraction over
`d₁·d₂`, and halving a fraction is simply *doubling its denominator* (`n/d / 2 = n/(2d)`), so no
`gcd`/reduction step is ever needed — `decodeRat`'s own `mkRat` call normalizes the result. -/

end DomainTheory.NeighbourhoodSystems

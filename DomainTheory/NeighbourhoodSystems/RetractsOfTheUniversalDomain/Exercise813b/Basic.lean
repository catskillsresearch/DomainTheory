module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.Formula
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.evalV
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.evalSet
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.vars
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.SemanticEquiv
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.Lindenbaum
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.toSet
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.Entails
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.mem_evalSet_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.evalV_eq_of_agree
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.exists_bitsOf_agree
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.formulaSetoid
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.semanticEquiv_iff_evalSet_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.toSet_mk

@[expose] public section

/-!
# Exercise 8.13(b) (Scott 1981, PRG-19, Lecture VIII) — the Lindenbaum algebra bridge

`8.13`'s parenthetical gloss — "the free Boolean algebra on `ℵ₀`-generators (= **the Lindenbaum
algebra of propositional calculus**)" — equates *the algebra itself* with a syntactic quotient of
propositional formulas. `Exercise813a.lean` already built (and used, to answer `8.13`'s actual
"prove that `U` is isomorphic to..." content) a concrete realization of that algebra,
`{X : Set ℕ | GeneratedBy generator X}`. This file makes the parenthetical literal: a `Formula`
syntax, its semantics `evalV`, the Lindenbaum quotient `Formula ⧸ SemanticEquiv`, and a bijection
(`Lindenbaum.toSet`) from that quotient onto `Exercise813a.lean`'s concrete algebra — plus
`entails_iff_evalSet_subset`, showing the bijection also matches semantic entailment with `⊆`, i.e.
it is an order (not just a set) correspondence.

Per the scoping discussion, this is *optional/expository*: `8.13`'s actual "prove that..." content
was already fully answered by `Exercise813a.lean` alone. Nothing here changes that; it only makes
the naming in the parenthetical literal instead of asserted.

## What's proved

* `Formula`, `evalV` — a minimal propositional-logic syntax (`ℵ₀` variables) and its standard
  truth-valuation semantics.
* `evalSet` — the *same* recursion, interpreted in `Set ℕ` via `Exercise813a.lean`'s `generator`.
* `mem_evalSet_iff` — the bridge: `n ∈ evalSet φ ↔ evalV (fun i => n.testBit i) φ = true`.
* `generatedBy_iff_exists_evalSet` — `evalSet`'s range is exactly `GeneratedBy generator`.
* `SemanticEquiv`/the `Formula` `Setoid` — Scott's own equivalence relation for the Lindenbaum
  algebra (`φ ~ ψ` iff they agree under every valuation).
* `semanticEquiv_iff_evalSet_eq` — the one substantive lemma: semantic equivalence (quantifying
  over *all* `v : ℕ → Bool`) agrees with `evalSet`-equality (which only ever "tests" the countably
  many valuations arising from a natural number's own bits), because a single formula only
  mentions finitely many variables (`exists_bitsOf_agree` supplies a matching bit-derived
  valuation for any finite variable set).
* `Lindenbaum := Quotient (formulaSetoid)`, `Lindenbaum.toSet`, `Lindenbaum.toSet_injective`,
  `Lindenbaum.range_toSet` — **the headline**: `Lindenbaum` (Scott's Lindenbaum algebra of
  propositional calculus) bijects, via `toSet`, onto `{X | GeneratedBy generator X}`
  (`Exercise813a.lean`'s free Boolean algebra on `ℵ₀` generators).
* `entails_iff_evalSet_subset` — the bijection also matches semantic entailment with `⊆`, so it
  respects order (hence the Boolean-algebra structure), not just underlying sets.
-/

namespace DomainTheory.NeighbourhoodSystems

/-! ### The formula language and its two evaluations -/





/-! ### Only finitely many variables matter -/



/-! ### `SemanticEquiv`: the Lindenbaum equivalence relation -/




/-! ### `Lindenbaum`, the Lindenbaum algebra of propositional calculus -/




/-! ### The bijection also matches entailment with `⊆` -/

end DomainTheory.NeighbourhoodSystems

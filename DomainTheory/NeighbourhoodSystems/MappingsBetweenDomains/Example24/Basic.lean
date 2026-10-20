/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.SatisfiesRunEquations
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.del
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.out
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.runMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.del_nil
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.del_true
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.del_false
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.out_nil
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.out_false
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.out_true
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.del_append
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.out_append
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.out_mono

@[expose] public section

/-!
# Example 2.4 (Scott 1981, PRG-19, §2) — eliminating the first run of `1`'s, `g : B → B`

Scott's second approximable mapping reads a binary sequence left to right and "eliminates the first
consecutive run of `1`'s while copying all the other digits." Thus

`g(0ⁿ 1ᵏ 0 x) = 0ⁿ⁺¹ x`   (for `k > 0`),   `g(1^∞) = ⊥`,   `g(0ⁿ 1^∞) = 0ⁿ`.

It is instructive because it turns *total* inputs (e.g. `1^∞`) into *partial* outputs.

We give the **guaranteed finite output** `out : Σ* → Σ*` for each finite input prefix via a two-state
scan: `out` copies leading `0`'s and, on the first `1`, hands over to `del`, which swallows the run
of `1`'s and — on the terminating `0` — emits that single `0` and copies the rest verbatim. The
elementwise value on the finite element `↑(σΣ*)` is `↑((out σ)Σ*)`, so the neighbourhood relation is

`X g Y ↔ ∃ σ, X = σΣ* ∧ (out σ)Σ* ⊆ Y ∧ Y ∈ B`.

`out` is prefix-monotone (`out_mono`: `σ <+: σ' → out σ <+: out σ'`), which gives Definition
2.1(iii); (i) and (ii) are the principal-filter facts for the cone `(out σ)Σ*`. Constructive.

**Exercise 2.17, second half.** Scott also asks to show that `runMap` is *uniquely* determined
among approximable mappings by the four equations `g(0x) = 0g(x)`, `g(11x) = g(1x)`,
`g(10x) = 0x`, `g(1) = ⊥` (`SatisfiesRunEquations`). We check `runMap` itself satisfies them
(`runMap_satisfies`, using the two "shift formulas" `runMap_toElementMap_sigmaElt` /
`sigmaElt_runMap_toElementMap`, so the statement is non-vacuous) and then prove uniqueness
(`eq_runMap_of_satisfies`): the recursive core (`key`) pins down any such `g` on every principal
element `σ⊥`, peeling *one* token of `σ` at a time, mirroring `out`'s own case split; the base case
`σ = []` is the only place order theory (`B.bot_le`) enters, everything else being pure
substitution into the equations. Constructive except for the `by_cases` in `ApproximableMap.ext`
(`#print axioms ⊆ {propext, Classical.choice, Quot.sound}`). -/

namespace DomainTheory.NeighbourhoodSystems.Example24

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB









/-! ## `runMap`'s relation and elementwise value, read off cones (mirrors `Example23`). -/

/-! ## Exercise 2.17, second half — `runMap` is *uniquely* determined by its equations -/

end DomainTheory.NeighbourhoodSystems.Example24

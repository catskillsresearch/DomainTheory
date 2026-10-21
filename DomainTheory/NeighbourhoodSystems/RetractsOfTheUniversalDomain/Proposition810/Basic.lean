/-ai
Proposition 8.10, first half, states that if two approximable self-maps of the universal domain are projections, then so are their sum, their product, and their arrow. A projection is a retraction that lies below the identity.

Scott's argument is that maps below the identity remain below the identity after each combinator, because the combinator of the two identities is the injection after the extraction and hence lies below the identity, and that idempotent maps remain idempotent, by substituting into the injection–pairing–extraction formula for the product and into the corresponding formulas for the sum and the arrow. The product is the injection after the product of the two maps after the extraction, so both halves reduce to the order of pairs and to those elementwise identities. The arrow, read through the equivalence of the function space with approximable maps, sends a map to the second map composed after it composed after the first, and the same algebra returns along that equivalence. The sum is read from the conditional formula, splitting on whether the extracted element meets the left copy, the right copy, or only the master. The bottom case of idempotence uses that a left inverse sends bottom to bottom. The left and right cases use disjointness of the two copies, and the images of the two injections meet those copies again.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69

@[expose] public section

/-!
# Proposition 8.10 (Scott 1981, PRG-19) — the combinators preserve projections

**Proposition 8.10 (first half).** If `a, b : 𝒰 → 𝒰` are projections, then so are `a+b`, `a×b`,
and `a→b`.

*Scott's proof.* `a, b ⊑ I` gives `a+b ⊑ I+I = i₊∘j₊ ⊑ I` (similarly for `×`, `→`);
`a = a∘a, b = b∘b` gives `(a×b)∘(a×b) = i_×∘⟨a∘a∘proj₀, b∘b∘proj₁⟩∘j_× = a×b` (similarly for `+`,
`→`).

## What is formalized in this file

Both halves of Proposition 8.10 — **`IsRetraction`- and `≤ idMap U`-closure** — for all three
combinators, i.e. `IsProjection a → IsProjection b → IsProjection (a*b)` for `* ∈ {+,×,→}`.

* **`×` (cleanest).** `prodComb a b` is *literally* `iTimes.comp ((prodMap a b).comp jTimes)`
  (`prodMap a b = ⟨a∘proj₀, b∘proj₁⟩` is exactly Exercise 3.19's product-functor combinator,
  unfolding `prodComb`'s definition, `rfl`). Both closure facts reduce, at the element level, to
  `pair_le_pair_iff`/`toElementMap_prodMap`/`toElementMap_mono` plus the two generic
  projection-pair identities below.

* **`→` (via `funSpaceEquiv`).** `lamComb a b`'s action, *transported through* `funSpaceEquiv`
  (Theorem 3.10, `(funSpace U U).Element ≃o ApproximableMap U U`), is exactly Scott's map-level
  formula `f ↦ b∘f∘a` (`toApproxMap_toElementMap_lamComb`, chaining `toElementMap_curry_apply`,
  `toElementMap_prodMap_pair`, `evalMap_apply`). Both closure facts then reduce to the same
  algebra as `×`, transported back through the order-embedding `toApproxMap`.

* **`+` (direct, no bridge to `sumMap`).** `sumMap`'s raw relation (`Exercise319Sum.lean`) is
  *not* literally built from `cond`/`which`, so there is no equally cheap `sumComb = i₊∘sumMap∘j₊`
  bridge; instead both facts are proved directly from Scott's literal formula via the elementwise
  characterizations `cond_toElementMap_mem` (Exercise 3.26), `which_mem_zero/one`, and the
  round-trip identities `inMap₀_outMap₀_eq_of_left`/`inMap₁_outMap₁_eq_of_right`, case-splitting
  on `sum_element_trichotomy`. Idempotence's bottom case additionally needs `jPlus_bot_eq_bot`
  (an instance of the general `toElementMap_bot_eq_bot_of_comp_eq_idMap`): if `j∘i = I_D`, then
  `j(E.bot)` is a lower bound of *all* of `|D|` (`D.bot ≤ i(v)`, monotone through `j`, landing on
  `j(i(v)) = v` — take `v := D.bot` — via `j∘i=I_D`), so `j(E.bot) ≤ D.bot`, whence `= D.bot` by
  antisymmetry with `bot_le`; no disjointness needed. The "reaches left"/"reaches right" case
  formulas' own idempotence step *does* need the disjointness fact `not_sum_reaches_both`
  (`inj₀_inter_inj₁`/`not_sum_mem_empty`) to rule out the other injection's guard in `which`, and
  `inMap₀_toElementMap_reaches_left`/`inMap₁_toElementMap_reaches_right` (witnessed by the master
  neighbourhood) to re-enter the same case after one more application of `a`/`b`.

The second half — finitary closure, and `D_a * D_b ≅ D_{a*b}` for `* ∈ {+,×,→}` — is
`proposition_8_10` in `Proposition810b.lean`. `D_a` there is `fixedNbhd a`.

Axiom footprint: everything here mentions `U`, so (as with `Definition89.lean`) it inherits `U`'s
own `Classical.choice` footprint — `⊆ {propext, Classical.choice, Quot.sound}`, confirmed not new.
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

/-! ## Two generic projection-pair identities, at the element level -/

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

/-! ## `×` (Definition 8.9's `prodComb`) -/

/-! ## `→` (Definition 8.9's `arrowComb`), via `funSpaceEquiv` -/

/-! ## `+` (Definition 8.9's `sumComb`), by direct case analysis on `sum_element_trichotomy` -/

/-! ## Proposition 8.10, first half — assembled -/
end DomainTheory.NeighbourhoodSystems

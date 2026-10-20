/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.swapProdT
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.pairToFun
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.funToPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.sumToProdT

@[expose] public section

/-!
# Exercise 8.19 (Scott 1981, PRG-19)

> **Exercise 8.19.** Suppose we know both `T` and `E→E ⊴ E`. Does it follow that `E+E` and
> `E×E ⊴ E`?

Here `T` is the truth-value domain of Example 1.2 (`Example23.T`/`Exercise326.TD`, the same
two-point-plus-bottom domain used throughout §3 for `cond`). Reading "we know `T`" as "we know
`T ⊴ E`" (the natural companion hypothesis to `E→E ⊴ E`, and exactly what is needed to make the
argument below go through), the answer is **yes**, both follow, via two general-purpose `⊴`
constructions:

* **Products.** `T ⊴ E` gives an embedding `E × E ⊴ (T → E)` (pair `(x, y)` up as the function
  `t ↦ cond(t, x, y)`, using Exercise 3.26's `cond`), and `T ⊴ E` gives `(T → E) ⊴ (E → E)`
  (precompose with the retraction `E → T`, contravariant functoriality of `expMap`,
  `Proposition810b.lean`). Chaining with the hypothesis `E → E ⊴ E` and `⊴`'s transitivity
  (Exercise 8.17) gives `E × E ⊴ E`.
* **Sums.** `T ⊴ E` similarly gives `E + E ⊴ T × (E × E)` (tag a summand by `which : E+E → T`
  together with the two projections `out₀, out₁ : E + E → E`, Exercise 3.26's `which`/`cond`
  machinery) and `T × (E × E) ⊴ E × (E × E)` (the *covariant* functoriality of `prod` in `T ⊴ E`).
  Composing with `E × E ⊴ E` (just proved, applied twice to peel off the nested product) and
  transitivity gives `E + E ⊴ E`.

Both directions reuse only pre-existing combinators (`cond`, `which`, `curry`, `evalMap`,
`expMap`, `paired`/`proj₀`/`proj₁`) — the only genuinely new general-purpose facts are `expMap`'s
monotonicity in its contravariant argument (`expMap_mono_left`), the analogous covariant
monotonicity of pairing (`prod_left_trianglelefteq`/`prod_right_trianglelefteq`), and two small
"cross" round-trip facts for the sum injections (`outMap₁_comp_inMap₀`/`outMap₀_comp_inMap₁`, the
natural companions of Exercise 3.18's `outMap₀_comp_inMap₀`/`outMap₁_comp_inMap₁`).

Everything here inherits `Classical.choice` only from `ext_of_toElementMap` calls already baked
into `expMap`'s own defining lemmas (`Proposition810b.lean`) and from `T`'s concrete presentation
(`Example12.lean`) — the same pre-existing footprint as every other `T`/`cond`-mentioning theorem
in the project, not something new introduced here.
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u

/-! ## General-purpose lemmas -/

section General

variable {α β γ δ : Type*}

end General

/-! ## Cross round-trips for the sum injections (companions of Exercise 3.18) -/

section SumHelpers

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

end SumHelpers

/-! ## Goal 1: `T ⊴ E` and `E → E ⊴ E` give `E × E ⊴ E` -/

section Prod

variable {α : Type u} {E : NeighborhoodSystem α}




end Prod

/-! ## Goal 2: `T ⊴ E` and `E → E ⊴ E` give `E + E ⊴ E` -/

section Sum

variable {α : Type u} {E : NeighborhoodSystem α} (hE : ∀ X, E.mem X → X.Nonempty)


end Sum

/-! ## Exercise 8.19, assembled -/
end DomainTheory.NeighbourhoodSystems

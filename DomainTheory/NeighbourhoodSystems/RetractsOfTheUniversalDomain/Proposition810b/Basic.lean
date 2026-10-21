/-ai
This file gathers and re-exports the infrastructure for the second half of Proposition 8.10. It includes the element isomorphism of a projection pair; the product, sum, and arrow injections and extractions between the combinator of the fixed neighbourhoods and the universal domain, with both composites; the exponential of maps, its elementwise form, its agreement with the lambda combinator, and its identity and composition laws; and the elementwise and functorial laws of the sum of maps, including bottom, the two copies, the two injections, the identity and composition laws, and the identification of the sum combinator with the sum injection after the sum of the maps after the sum extraction.

Proposition 8.10, second half, states that if two self-maps of the universal domain are finitary projections, then so are their sum, product, and arrow, and the fixed neighbourhood of each combinator is order-isomorphic to the corresponding combinator of the fixed neighbourhoods. For a finitary projection the map is the retraction of its fixed neighbourhood, hence the injection after the projection of that subsystem. A projection pair whose extraction after the injection is the identity induces an order isomorphism from the domain onto the fixed elements of the injection after the extraction. Each combinator is realized by transporting the fixed injection and extraction of the universal domain through the functorial action of that combinator on the two subsystem injections and projections.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.elementIsoOfProjectionPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.IProdComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.JProdComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.prodComb_elementIso
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.ISumComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.JSumComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.sumComb_elementIso
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.expMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.IArrowComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.JArrowComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.arrowComb_elementIso
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.toElementMap_bot_eq_bot_of_comp_le_idMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.fixedNbhd_mem_nonempty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.inj_comp_proj_eq_self
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.JProdComb_comp_IProdComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.IProdComb_comp_JProdComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.reaches_neither_iff_eq_bot
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.sumMap_bot
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.sumMap_reaches_left
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.sumMap_reaches_right
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.toElementMap_sumMap_inMap₀
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.toElementMap_sumMap_inMap₁
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.toElementMap_sumMap_of_left
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.toElementMap_sumMap_of_right
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.sumMap_id
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.sumMap_comp
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.sumComb_eq_iPlus_sumMap_jPlus
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.JSumComb_comp_ISumComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.ISumComb_comp_JSumComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.expMap_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.expMap_eq_lamComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.toApproxMap_toElementMap_expMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.expMap_id
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.expMap_comp
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.JArrowComb_comp_IArrowComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.IArrowComb_comp_JArrowComb

@[expose] public section

/-!
# Proposition 8.10 (Scott 1981, PRG-19), second half — finitary-closure

**Proposition 8.10(b).** If `a, b : 𝒰 → 𝒰` are finitary (projections), then so are `a+b`, `a×b`,
`a→b`, and moreover `D_{a+b} ≅ D_a + D_b`, `D_{a×b} ≅ D_a × D_b`, `D_{a→b} ≅ (D_a → D_b)`, where
`D_a`, `D_b` are the (witnessing) domains of `a`, `b`.

## Strategy

For a finitary projection `a : 𝒰 → 𝒰`, Theorem 8.6's `sub_eq_self_of_isFinitaryProjection` gives
`a = retractionOfSubsystem (fixedNbhd_subsystem a)`, i.e. `a = i_a ∘ j_a` for the canonical
injection/projection pair `i_a : D_a → 𝒰`, `j_a : 𝒰 → D_a` of Proposition 6.12, where
`D_a := fixedNbhd a` is a genuine subsystem of `𝒰` (Theorem 8.5). This is Scott's "`D_a`" made
concrete and computed with directly (rather than via the abstract `IsFinitary` witness).

The key generic tool (`elementIsoOfProjectionPair` below) is Proposition 8.2's `elementIso`,
generalized away from requiring a literal `D ◁ E` subset relation to an *arbitrary* approximable
projection pair `i : D → E`, `j : E → D` with `j ∘ i = I_D` (no requirement `i ∘ j ≤ I_E`, and no
requirement that `D`, `E` share a token type) — exactly what `theorem_8_8_b_strong`'s fixed maps
`i₊/j₊`, `i_×/j_×`, `i_→/j_→` (Definition 8.9) are. Given such a pair and `g = i.comp j`, it
produces `D.Element ≃o Fix(g)` directly.

For each combinator `* ∈ {+, ×, →}` we build a *new* projection pair `I : D_a * D_b → 𝒰`,
`J : 𝒰 → D_a * D_b` (composing Definition 8.9's fixed maps with the functorial action of `*` on
`i_a, j_a, i_b, j_b`) and show algebraically (via the functor laws of `×`/`+`/`→` on maps, plus
`i_a.comp j_a = a`, `i_b.comp j_b = b`) that `J.comp I = idMap (D_a * D_b)` and
`I.comp J = a * b`. `elementIsoOfProjectionPair` then hands us
`(D_a * D_b).Element ≃o Fix(a * b)` directly, both witnessing `IsFinitary (a * b)` and Scott's
"moreover" isomorphism claim in one shot.

* **`×`** uses Exercise 3.19/3.20's `prodMap` and its functor laws `prodMap_id`/`prodMap_comp`
  directly — no new infrastructure needed.
* **`+`** needs a modest amount of new infrastructure for `sumMap` (Exercise 3.19's sum functor):
  its own elementwise case-split formulas (mirroring `Proposition810.lean`'s `sumComb` formulas)
  and its functor laws `sumMap_id`/`sumMap_comp`, built here.
* **`→`** needs a generalization of `lamComb`'s construction (`expMap`, the Hom-functor's action
  `f ↦ k ∘ f ∘ h`) away from self-maps of `𝒰` to a genuine bifunctor `funSpace V₀ V₁ →
  funSpace V₀' V₁'` for `h : V₀' → V₀`, `k : V₁ → V₁'`, together with its functor laws.

Axiom footprint: everything here mentions `U`, so it inherits `U`'s own `Classical.choice`
footprint, `⊆ {propext, Classical.choice, Quot.sound}`, confirmed not new (same as
`Proposition810.lean`/`Definition89.lean`).
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u

/-! ## A generic projection-pair `elementIso`, without requiring a literal `◁` subset relation -/

variable {α β : Type u} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}


/-! ## Setup: `D_a := fixedNbhd a`, the concrete witnessing domain of a finitary projection `a` -/

variable {a b : ApproximableMap U U}


/-! ## The `×` case -/

section ProdCase

variable (a b : ApproximableMap U U)


end ProdCase

/-! ## `sumMap` infrastructure: elementwise formulas and functoriality

Exercise 3.19's sum functor `sumMap` is not literally built from `cond`/`which` (unlike
`prodMap`), so its elementwise behaviour and functor laws (`sumMap_id`/`sumMap_comp`) are
established here directly, mirroring `Proposition810.lean`'s treatment of `sumComb` itself. -/

section SumMapLemmas

variable {γ δ γ' δ' γ'' δ'' : Type u}
variable {V0 : NeighborhoodSystem γ} {V1 : NeighborhoodSystem δ}
variable {V0' : NeighborhoodSystem γ'} {V1' : NeighborhoodSystem δ'}
variable {V0'' : NeighborhoodSystem γ''} {V1'' : NeighborhoodSystem δ''}
variable {h0 : ∀ X, V0.mem X → X.Nonempty} {h1 : ∀ Y, V1.mem Y → Y.Nonempty}
variable {h0' : ∀ X, V0'.mem X → X.Nonempty} {h1' : ∀ Y, V1'.mem Y → Y.Nonempty}
variable {h0'' : ∀ X, V0''.mem X → X.Nonempty} {h1'' : ∀ Y, V1''.mem Y → Y.Nonempty}


end SumMapLemmas

/-! ## The `+` case

Unlike the `×` case, `sumComb` is *not* literally `iPlus.comp ((sumMap a b).comp jPlus)` by
`rfl` (Definition 8.9 builds it from `cond`/`whichMap` instead) — but it *is* that map
elementwise (`sumComb_eq_iPlus_sumMap_jPlus` below), by the exact same case-split already used
for `isRetraction_sumComb`/`le_idMap_sumComb` in `Proposition810.lean`. Given that bridge, the
rest is verbatim the `×` case's algebra, now powered by `sumMap_id`/`sumMap_comp`. -/

section SumCase

variable (a b : ApproximableMap U U)


end SumCase

/-! ## `expMap`: the Hom-bifunctor `(𝒟₀→𝒟₁) → (𝒟₀'→𝒟₁')`, for `h : 𝒟₀'→𝒟₀`, `k : 𝒟₁→𝒟₁'`

Generalizes `lamComb`'s construction (`Definition89.lean`) — the Hom-functor's action on maps,
`f ↦ k∘f∘h` — away from self-maps of `𝒰` (`lamComb a b = expMap a b`, `expMap_eq_lamComb` below)
to a genuine bifunctor on approximable maps between arbitrary neighbourhood systems, contravariant
in `h` and covariant in `k`. -/

section ExpMap

variable {γ δ γ' δ' γ'' δ'' : Type*}
variable {V0 : NeighborhoodSystem γ} {V1 : NeighborhoodSystem δ}
variable {V0' : NeighborhoodSystem γ'} {V1' : NeighborhoodSystem δ'}
variable {V0'' : NeighborhoodSystem γ''} {V1'' : NeighborhoodSystem δ''}


end ExpMap

/-! ## The `→` case -/

section ArrowCase

variable (a b : ApproximableMap U U)


end ArrowCase

/-! ## Proposition 8.10(b) — assembled -/
end DomainTheory.NeighbourhoodSystems

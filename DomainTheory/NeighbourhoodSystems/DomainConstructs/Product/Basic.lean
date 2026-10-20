/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prod
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.fst
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.snd
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.pair
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prodEquiv
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.proj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.proj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.paired
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.constMap
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.toMap₂
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.ofMap₂
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.map₂Equiv
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.mem_prodNbhd_inl
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.mem_prodNbhd_inr
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.inl_preimage_prodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.inr_preimage_prodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prodNbhd_inter
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prodNbhd_subset_iff
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prodNbhd_injective
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prod_mem_iff
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prod_mem_prodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prod_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.mem_fst
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.mem_snd
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prod_mem_split
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.mem_pair
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.mem_pair_prodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.pair_fst_snd
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.fst_pair
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.snd_pair
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prodEquiv_apply
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prodEquiv_symm_apply
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prodNbhd_preimage
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.proj₀_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.proj₁_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.paired_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.toElementMap_proj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.toElementMap_proj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prod_mem_prodNbhd_iff
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.constMap_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.toElementMap_constMap
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.ext
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.toMap₂_ofMap₂
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.ofMap₂_toMap₂

@[expose] public section

/-!
# Lecture III (§3) — the product system: Definitions 3.1, 3.3, Propositions 3.2, 3.4,
Lemma 3.6, Theorems 3.5, 3.7

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19 (1981), Lecture III,
*Constructions on domains*. Given two neighbourhood systems over **disjoint** token sets `Δ₀`, `Δ₁`,
the **product system** `𝒟₀ × 𝒟₁` has neighbourhoods `X ∪ Y` (`X ∈ 𝒟₀`, `Y ∈ 𝒟₁`) over `Δ₀ ∪ Δ₁`.

We model the disjoint union of token sets by the **sum type** `α ⊕ β`, and the product
neighbourhood `X ∪ Y` by `prodNbhd X Y = Sum.inl '' X ∪ Sum.inr '' Y`. Because `Sum.inl` and
`Sum.inr` have disjoint ranges, the cleanest facts of Scott's proof become transparent:

* `prodNbhd_inter` — `(X ∪ Y) ∩ (X' ∪ Y') = (X ∩ X') ∪ (Y ∩ Y')` (Scott's (2));
* `prodNbhd_subset_iff` — `X ∪ Y ⊆ X' ∪ Y' ↔ X ⊆ X' ∧ Y ⊆ Y'` (Scott's (1));
* `prodNbhd_injective` — the representation `X ∪ Y` is unique.

This file formalizes:

* **Definition 3.1 / Proposition 3.2** — the product system `prod V₀ V₁`, the element pairing
  `pair x y = ⟨x, y⟩`, the order law `pair_le_pair_iff` (3.2(i)), and the order-isomorphism
  `prodEquiv : |𝒟₀ × 𝒟₁| ≃o |𝒟₀| × |𝒟₁|`.
* **Definition 3.3 / Proposition 3.4** — projections `proj₀`, `proj₁`, the paired mapping `paired f g`,
  and `proj₀_comp_paired`, `proj₁_comp_paired`, `paired_proj` (`⟨p₀∘h, p₁∘h⟩ = h`),
  `toElementMap_paired` (`⟨f, g⟩(w) = ⟨f(w), g(w)⟩`).
* **Lemma 3.6** — constant maps `constMap b` (`X b Y ↔ Y ∈ b`) with `toElementMap_constMap`.
* **Theorem 3.5** — joint vs. separate approximability, via the bridge `ApproximableMap (prod V₀ V₁) V₂
  ≃ ApproximableMap₂ V₀ V₁ V₂` (`ofMap₂` / `toMap₂` and round-trips).
* **Proposition 3.7** — multivariate approximable functions are closed under substitution
  (`comp`/`paired`/`proj` bookkeeping).

Everything is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}










variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}




/-! ### Projections of an element (Scott's `z₀`, `z₁`). -/






/-! ### Definition 3.1 — the element pairing `⟨x, y⟩`. -/










/-! ### Definition 3.3 / Proposition 3.4 — projections and pairing of maps. -/

variable {V₂ : NeighborhoodSystem γ}

open ApproximableMap











/-! ### Lemma 3.6 — constant maps. -/




/-! ### Theorem 3.5 — joint vs. separate approximability. -/







/-! ### Proposition 3.7 — closure under substitution. -/

variable {V₃ : NeighborhoodSystem δ}
end DomainTheory.NeighbourhoodSystems

/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise214.phi

@[expose] public section

/-!
# Exercise 2.14 (Scott 1981, PRG-19, §2) — the neighbourhood correspondence `φ` of an isomorphism

> **EXERCISE 2.14.** Let `f : |𝒟₀| → |𝒟₁|` be an isomorphism between domains. Let `φ : 𝒟₀ → 𝒟₁` be
> the one-one correspondence between neighbourhoods provided by Theorem 2.7 where `f(↑X) = ↑φ(X)`
> for all `X ∈ 𝒟₀`. Show that the approximable mapping determined by `f` is just the relationship
> `φ(X) ⊆ Y`. In addition prove that if `X, X' ∈ 𝒟₀` are consistent, then
> `φ(X ∩ X') = φ(X) ∩ φ(X')`.
> Remark that the isomorphisms between domains correspond exactly to the isomorphisms between
> neighbourhood systems (in the sense of one-one inclusion preserving correspondences).

Theorem 2.7 (`exists_principal_eq_apply_principal`) says a domain isomorphism `e : |𝒟₀| ≃o |𝒟₁|`
carries each finite element `↑X` to a finite element `↑Y`. We extract the witness `Y` by
`Classical.choose`, getting `φ` with `φ_spec : e(↑X) = ↑φ(X)`:

* `phi e hX`, `phi_mem`, `phi_spec` — the neighbourhood correspondence `φ` of `e`.
* `rel_ofIso_iff` — the approximable mapping of `e` is exactly `φ(X) ⊆ Y`:
  `(ofIso e).rel X Y ↔ 𝒟₁ Y ∧ φ(X) ⊆ Y` (for `X ∈ 𝒟₀`).
* `phi_inter` — **`φ(X ∩ X') = φ(X) ∩ φ(X')`** for *consistent* `X, X'` (i.e. `X ∩ X' ∈ 𝒟₀`).
  The proof goes through the order structure: `↑(X ∩ X')` is the **least upper bound** (join) of
  `↑X, ↑X'` in `|𝒟₀|` (note the inclusion order is *reversed*); `e` and `e.symm` are monotone, so
  they preserve this join, and the join of two consistent principals `↑A, ↑B` in `|𝒟₁|` is
  `↑(A ∩ B)`.

`φ` is `Classical.choose`-based, hence `noncomputable` and classical; the order-theoretic proofs of
`rel_ofIso_iff`/`phi_inter` are otherwise choice-free (`propext`, `Quot.sound`). -/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

end DomainTheory.NeighbourhoodSystems

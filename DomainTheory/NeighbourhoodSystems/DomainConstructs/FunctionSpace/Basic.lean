/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.step
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.stepFun
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.funSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.toApproxMap
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.toFilter
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.funSpaceEquiv
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.interYs
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.leastMap
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.MapsBounded
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.PointwiseBounded
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.supOnPrincipal
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.sSupMaps
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.eval
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.evalMap
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.gSection
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.curry
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.uncurry
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.curryEquiv
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.BasicInst3
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.mem_step
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.mem_stepFun
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.stepFun_nil
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.stepFun_cons
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.stepFun_append
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.stepFun_singleton
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.step_master_eq
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.step_inter_right
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.step_subset
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.funSpace_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.funSpace_mem_iff
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.step_mem
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.mem_stepFun_iff
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.toApproxMap_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.mem_toFilter
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.funSpaceEquiv_apply
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.funSpaceEquiv_symm_apply
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.funSpace_mem_inter
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.stepFun_up_closed
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.funSpace_mem_up_closed
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.interYs_nil
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.interYs_cons
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.mem_interYs
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.interYs_subset_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.interYs_antitone
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.leastMap_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.mapsBounded_principal
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.supOnPrincipal_mono
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.gSection_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.gSection_le
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.curry_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.rel_stepFun_iff
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.prod_mem_inl
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.prod_mem_inr
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.uncurry_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.uncurry_curry
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.curry_uncurry

@[expose] public section

/-!
# Lecture III (§3) — the function space `(𝒟₀ → 𝒟₁)`: Definitions 3.8, Propositions 3.9,
Theorems 3.10, 3.11, 3.12, 3.13

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19 (1981), Lecture III.
The **function space** `(𝒟₀ → 𝒟₁)` is the neighbourhood system whose *tokens* are the approximable
maps `𝒟₀ → 𝒟₁` (Definition 2.1), and whose neighbourhoods are the non-empty finite intersections of
the *step sets*

`[X, Y] = {f ∣ X f Y}`   (`step X Y`),

for `X ∈ 𝒟₀`, `Y ∈ 𝒟₁`. We model a finite intersection by a `List` of `(X, Y)` pairs, with
`stepFun L = {f ∣ ∀ (X, Y) ∈ L, X f Y}`; the empty list gives the master `Δ = |𝒟₀ → 𝒟₁|`
(`Set.univ`). The system is **positive**: a neighbourhood is required non-empty, which is exactly
what makes a filter's induced relation *intersective* (Theorem 3.10).

This file formalizes:

* **Definition 3.8** — `step`, `stepFun`, the system `funSpace V₀ V₁`, with the basic algebra
  `step_inter_right` (`[X,Y] ∩ [X,Y'] = [X,Y∩Y']`), `step_subset` (antitone/monotone),
  `step_master_eq` (`[Δ₀,Δ₁] = univ`), and membership `step_mem`.
* **Theorem 3.10** (the crux) — `funSpaceEquiv : |𝒟₀ → 𝒟₁| ≃o ApproximableMap V₀ V₁`: every filter
  is fixed by a unique approximable map (`toApproxMap`/`toFilter`), inclusion-preservingly.
* **Proposition 3.9** — `leastMap` (the least map `f₀` of a consistent neighbourhood, condition
  (ii) `X f₀ Y ↔ ⋂{Yᵢ ∣ X ⊆ Xᵢ} ⊆ Y`), `leastMap_mem_stepFun` and `leastMap_le` (it is the minimal
  element of `⋂[Xᵢ,Yᵢ]`), and `stepFun_subset_step_iff` (the remark after 3.9). The consistency
  hypothesis `hcons` is Scott's condition (i) in operational form.
* **Theorem 3.13** — `le_iff_toElementMap_le` (i); `mapsBounded_iff_pointwiseBounded` (ii);
  `sSupMaps` with `toElementMap_sSupMaps` (iii).
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-! ### The order on approximable maps (rel-inclusion). -/


/-! ### Definition 3.8 — step sets and the function space. -/

















/-! ### Theorem 3.10 — the function space is complete. -/











/-! ### Proposition 3.9 — the least map of a consistent neighbourhood. -/









/-! ### Theorem 3.13(i) — the pointwise order. -/

/-! ### Theorem 3.13(ii)(iii) — pointwise boundedness and sups. -/







/-! ### Theorem 3.11 — evaluation. -/

variable {V₂ : NeighborhoodSystem γ}



/-! ### Theorem 3.12 — currying. -/













end DomainTheory.NeighbourhoodSystems

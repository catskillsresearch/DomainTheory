/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise222
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.graph
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.C
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.meetMap
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.joinMap
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.graphEquiv
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.funSpaceReprIso
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.mem_graph
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.graph_injective
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.C_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.sInter_eq_graph_meetMap
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.C_inter
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.sUnion_eq_graph_joinMap
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.C_dir

@[expose] public section

/-!
# Exercise 3.27 (Scott 1981, PRG-19, §3) — `(𝒟₀ → 𝒟₁)` is a domain, via Exercise 2.22

(*For set theorists.*) Scott asks for *another* proof that the family of approximable mappings
`f : 𝒟₀ → 𝒟₁` is isomorphic to a domain, "by employing the general argument of Exercise 2.22"
(the abstract representation theorem: any family of sets closed under non-empty intersections and
directed unions is inclusion-isomorphic to a domain).

The set-theoretic content: identify each approximable map `f` with its **graph**
`graph f = {(X, Y) ∣ X f Y} ⊆ 𝒫(Δ₀) × 𝒫(Δ₁)`, and let `C = {graph f}` be the family of all such
graphs. Then

* `C` is closed under **non-empty intersections** — the pointwise *meet* `⋀ 𝒮` of a family of
  approximable maps (relate `X` to `Y` iff every member does) is again approximable (`meetMap`);
* `C` is closed under **directed unions** — the *join* `⋁ 𝒮` of a directed family (relate `X` to `Y`
  iff some member does) is again approximable, the consistency condition using directedness
  (`joinMap`).

So Exercise 2.22 (`reprIso`) re-presents `C` — hence, via `graph` and Theorem 3.10 (`funSpaceEquiv`),
the whole function space `|𝒟₀ → 𝒟₁|` — as the domain of a neighbourhood system, *without* writing
down the step-set neighbourhoods of Definition 3.8 explicitly. This is exactly Scott's "compare with
3.9/3.10" alternative.

**Axioms.** As flagged by Scott ("for set theorists"), this inherits `Classical.choice` from
Exercise 2.22 and from the `graph`-inversion.
-/

namespace DomainTheory.NeighbourhoodSystems.Exercise327

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}






/-! ### The meet of a non-empty family of maps. -/




/-! ### The join of a directed family of maps. -/




/-! ### `C ≅ Hom(𝒟₀, 𝒟₁) ≅ |𝒟₀ → 𝒟₁|`. -/


/-! ### Exercise 3.27. -/


end DomainTheory.NeighbourhoodSystems.Exercise327

module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise122
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.sierpinski
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.mapOfOpen
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.openOfMap
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.openIso
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.opensReprIso
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.mapOfOpen_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.mapOfOpen_rel_empty
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.openOfMap_isOpen

@[expose] public section

/-!
# Exercise 3.25 (Scott 1981, PRG-19, §3) — the open sets of `|𝒟|` form a domain

(*For topologists.*) Exercises 1.21/1.22 and 2.13 regard a domain `|𝒟|` as a topological space (the
basic opens `[X] = {x ∣ X ∈ x}`, `basicOpen`) on which the approximable maps are exactly the
continuous functions. Scott asks, "using 3.10", to show that **the family of open subsets of `|𝒟|`
is isomorphic to a domain.**

The route is the standard "open sets = maps to Sierpiński space". Let `𝒪` be the **Sierpiński
domain** (`sierpinski`): the two-token-state system whose neighbourhoods are `Δ = univ` and `∅`, so
`|𝒪|` is the two-element domain `⊥ ⊏ ⊤`. The correspondence

* `mapOfOpen U` : `𝒟 → 𝒪`, relating `X` to `∅` (the "defined"/top neighbourhood of `𝒪`) exactly when
  `[X] ⊆ U`, and to `univ` always;
* `openOfMap f = {x ∣ f(x) = ⊤} = ⋃ {[X] ∣ X f ∅}`;

are mutually inverse and inclusion-preserving (`openIso`), so by **Theorem 3.10** (`funSpaceEquiv`,
`|𝒟 → 𝒪| ≃ ApproximableMap`) the lattice of open sets is order-isomorphic to the domain
`|𝒟 → 𝒪|` (`opensReprIso`). The one place topology (openness of `U`) is used is the round trip
`openOfMap (mapOfOpen U) = U` and the `←` half of order reflection: an open set is recovered from its
basic neighbourhoods.
-/

namespace DomainTheory.NeighbourhoodSystems.Exercise325

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set


variable {α : Type*} (V : NeighborhoodSystem α)

/-! ### From an open set to an approximable map `𝒟 → 𝒪`. -/




/-! ### From an approximable map `𝒟 → 𝒪` to an open set. -/



/-! ### The order-isomorphism `Opens(|𝒟|) ≃o (𝒟 → 𝒪)`. -/



end DomainTheory.NeighbourhoodSystems.Exercise325

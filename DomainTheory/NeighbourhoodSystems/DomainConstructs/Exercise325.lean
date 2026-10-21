/-ai
This file gathers and re-exports the correspondence of Exercise 3.25 between open sets of a domain and approximable maps into Sierpiński space: the map of an open set and its relation, including the empty case, the open set of a map and its openness, and the two order isomorphisms.

The set of elements sent to the top by an approximable map into the Sierpiński domain is an open set of elements.

The numbered name example_325 is that statement.
ai-/
module

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

namespace DomainTheory.NeighbourhoodSystems.Exercise325

set_option linter.unusedVariables false

theorem example_325.{u_1} : ∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
  (f :
    @DomainTheory.NeighbourhoodSystems.ApproximableMap α Unit V
      DomainTheory.NeighbourhoodSystems.Exercise325.sierpinski),
  @IsOpen (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement α V)
    (@DomainTheory.NeighbourhoodSystems.Exercise325.openOfMap α V f) :=
  @DomainTheory.NeighbourhoodSystems.Exercise325.openOfMap_isOpen

end DomainTheory.NeighbourhoodSystems.Exercise325

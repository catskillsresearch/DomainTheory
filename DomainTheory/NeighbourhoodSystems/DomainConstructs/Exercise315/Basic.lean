/-ai
This file gathers and re-exports the product order-isomorphism helpers, the commutativity and associativity maps, the terminal domain and its two unit laws, uniqueness of the terminal element, and congruence of the product under order isomorphism.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315.prodCongrOrderIso
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315.prodUniqueOrderIso
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315.uniqueProdOrderIso
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315.prodCommD
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315.prodAssocD
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315.unitSys
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315.prodUnitD
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315.unitProdD
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315.prodCongrD
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315.unitSys_element_eq
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315.BasicInst12

@[expose] public section

/-!
# Exercise 3.15 (Scott 1981, PRG-19, §3) — the usual product isomorphisms

Scott asks for the standard isomorphisms of the product construction. Because Proposition 3.2 gives
the order-isomorphism `prodEquiv : |𝒟₀ × 𝒟₁| ≃o |𝒟₀| × |𝒟₁|`, every isomorphism reduces to the
corresponding fact about cartesian products of *ordered sets*: mathlib's `OrderIso.prodComm` and
`OrderIso.prodAssoc`, together with the two product congruences `prodCongrOrderIso` /
`prodUniqueOrderIso` we record here.

* **(i)** `𝒟₀ × 𝒟₁ ≅ 𝒟₁ × 𝒟₀` — `prodCommD`.
* **(ii)** `𝒟₀ × (𝒟₁ × 𝒟₂) ≅ (𝒟₀ × 𝒟₁) × 𝒟₂` — `prodAssocD`.
* **The product of no factors** is the one-point (terminal) domain `𝟙 = unitSys`; it is a two-sided
  unit for `×`: `𝒟 × 𝟙 ≅ 𝒟 ≅ 𝟙 × 𝒟` (`prodUnitD`, `unitProdD`).
* **(iii)** `𝒟₀ ≅ 𝒟₀'` and `𝒟₁ ≅ 𝒟₁'` imply `𝒟₀ × 𝒟₁ ≅ 𝒟₀' × 𝒟₁'` — `prodCongrD` /
  `Isomorphic.prod`.

Everything is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}

/-! ### Order-iso helpers for cartesian products. -/




/-! ### (i) Commutativity. -/


/-! ### (ii) Associativity. -/


/-! ### The product of no factors — the terminal (one-point) domain. -/






/-! ### (iii) Functoriality of `≅`. -/

end DomainTheory.NeighbourhoodSystems

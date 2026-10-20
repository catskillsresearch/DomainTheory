/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise323.toUnit
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise323.homAdjunction
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise323.BasicInst4
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise323.BasicInst5

@[expose] public section

/-!
# Exercise 3.23 (Scott 1981, PRG-19, §3) — the category of domains is cartesian closed

Exercise 3.23 asks (for category theorists) to read off from Theorems 3.11 and 3.12 that the category
of domains and approximable mappings is *cartesian closed*, to identify its terminal object, and to
say what sort of functor `(𝒟₀ → 𝒟₁)` is.

The three ingredients are already in the development; this file packages them and supplies the
missing terminal object:

* **Terminal object.** The one-point domain `𝟙 = unitSys` (Exercise 3.15) is *terminal*: there is a
  unique approximable mapping `𝒟 → 𝟙` (`Unique (ApproximableMap V unitSys)`), because `|𝟙|` is a
  subsingleton.
* **Finite products.** `prod` with `proj₀`, `proj₁` is the categorical product (Exercise 3.20).
* **Exponentials.** `curryEquiv` (Theorem 3.12) is the natural adjunction
  `Hom(𝒟₀ × 𝒟₁, 𝒟₂) ≃o Hom(𝒟₀, (𝒟₁ → 𝒟₂))`, exhibiting `(𝒟₁ → 𝒟₂)` as the exponential `𝒟₂^𝒟₁`.

So `𝟙`, `×`, and `→` make the category cartesian closed, and `(𝒟₀ → -)` is a (covariant) functor
right adjoint to `- × 𝒟₀`. Everything is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} (V : NeighborhoodSystem α)
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-! ### The terminal domain. -/




/-! ### The exponential adjunction (cartesian closure). -/

end DomainTheory.NeighbourhoodSystems

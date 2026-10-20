/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise122
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213.ofContinuous
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213.continuous_monotone
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213.BasicInst8

@[expose] public section

/-!
# Exercise 2.13 (Scott 1981, PRG-19, §2) — approximable maps **are** the continuous functions

> **EXERCISE 2.13.** (For topologists.) Recall Exercise 1.22 where it was shown that any domain
> `|𝒟|` is a topological space. Prove from Exercise 2.9 that the functions `f : |𝒟₀| → |𝒟₁|`
> determined by approximable mappings are exactly *the continuous functions between these spaces.*

This file closes the loop between the §2 theory of approximable mappings (`Approximable.lean`,
`ApproximableExercises.lean`) and the Exercise 1.22 topology on `|𝒟|` (`Exercise122.lean`):

* **`continuous_toElementMap`** — every approximable mapping `f` induces a *continuous* function
  `x ↦ f(x)`. Scott's hint: by Exercise 2.9, `f⁻¹[Y] = ⋃ {[X] ∣ Y ∈ f(↑X)}`, so the inverse image
  of a basic open is a union of basic opens, hence open.
* **`continuous_monotone`** — a continuous `c : |𝒟₀| → |𝒟₁|` is monotone for `⊑` (the order is the
  specialization order, `le_iff_isOpen_imp`).
* **`mem_iff_principal_of_continuous`** — Scott's union formula for a *continuous* `c`:
  `Y ∈ c(x) ↔ ∃ X ∈ x, Y ∈ c(↑X)`. (Forward: `c⁻¹[X]` open ∋ `x`; reverse: `↑X ⊑ x` + monotone.)
* **`ofContinuous`** — the approximable mapping of a continuous function, built from `ofMono` on the
  finite elements `↑X ↦ c(↑X)` (monotone by `continuous_monotone`).
* **`toElementMap_ofContinuous`** — the round trip: `ofContinuous c hc` induces exactly `c`
  (`(ofContinuous c hc)(x) = c(x)`), combining Exercise 2.9 with the union formula.

Together: `f ↦ toElementMap f` and `c ↦ ofContinuous c` exhibit approximable mappings `𝒟₀ → 𝒟₁`
and continuous functions `|𝒟₀| → |𝒟₁|` as the same thing.

Choice-free apart from the `ofMono`/Exercise-2.9 ingredients (whose uniqueness companions are the
only classical pieces). -/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

universe u

variable {α : Type u} {β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

namespace ApproximableMap

end ApproximableMap

namespace NeighborhoodSystem



end NeighborhoodSystem

namespace ApproximableMap

end ApproximableMap
end DomainTheory.NeighbourhoodSystems

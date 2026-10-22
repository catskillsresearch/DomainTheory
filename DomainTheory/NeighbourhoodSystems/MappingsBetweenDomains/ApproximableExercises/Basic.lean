/-ai
A neighbourhood belongs to the two-variable elementwise image of a pair of elements if and only if some neighbourhood of the first element and some neighbourhood of the second are jointly related to it.

This equivalence is the defining membership of the two-variable elementwise image.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import Mathlib.Data.Set.Image
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises.ApproximableMap₂
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises.iSupDirected
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises.ofMono
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises.interMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises.iSupMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises.toElementMap₂

@[expose] public section

/-!
# Lecture II (§2) — Exercises 2.8–2.12 and 2.19 (the algebra of approximable mappings)

Following Dana Scott, PRG-19 (1981), Lecture II. This file collects the *structural* exercises about
approximable mappings, all built on `Approximable.lean`:

* **Exercise 2.8** — an approximable map is determined by its action on finite (principal) elements
  (`eq_of_toElementMap_principal`); and **any** monotone function on finite elements extends to an
  approximable map (`ofMono`, `toElementMap_ofMono_principal`).
* **Exercise 2.9** — Scott's formula `f(x) = ⋃ {f(↑X) ∣ X ∈ x}` (`toElementMap_mem_iff_principal`).
* **Exercise 2.10** — the pointwise **meet** of two maps: `h(x) = f(x) ∩ g(x)` (`interMap`).
* **Exercise 2.11** — `|𝒟|` is closed under **directed unions** (`iSupDirected`, with
  `mem_iSupDirected`/`le_iSupDirected`/`iSupDirected_le`), and approximable maps **preserve** them
  (`toElementMap_iSupDirected`).
* **Exercise 2.12** — a directed family of approximable maps has a **pointwise union** that is again
  approximable (`iSupMap`, `mem_toElementMap_iSupMap`).
* **Exercise 2.19** — **two-variable** approximable maps `f : 𝒟₀ × 𝒟₁ → 𝒟₂` as ternary relations
  (`ApproximableMap₂`), with the Proposition 2.2 analogue (`toElementMap₂`, `rel₂_iff_mem_principal`).

All constructions are **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`); the two
`eq_of_…`/uniqueness lemmas decide membership by `by_cases` and are therefore classical, exactly like
`ext_of_toElementMap`. -/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ : Type*}

namespace NeighborhoodSystem


end NeighborhoodSystem

namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-! ### Exercise 2.8 — determination by, and extension from, finite elements. -/


/-! ### Exercise 2.9 — the elementwise map as a union over finite approximants. -/

/-! ### Exercise 2.10 — the pointwise meet of two approximable maps. -/


/-! ### Exercise 2.11 — approximable maps preserve directed unions. -/

/-! ### Exercise 2.12 — the pointwise union of a directed family of maps. -/


end ApproximableMap

/-! ### Exercise 2.19 — approximable mappings of two variables. -/


namespace ApproximableMap₂

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}


@[simp] theorem mem_toElementMap₂ (f : ApproximableMap₂ V₀ V₁ V₂) (x : V₀.Element) (y : V₁.Element)
    {Z : Set γ} : (f.toElementMap₂ x y).mem Z ↔ ∃ X Y, x.mem X ∧ y.mem Y ∧ f.rel X Y Z := Iff.rfl
end ApproximableMap₂
end DomainTheory.NeighbourhoodSystems

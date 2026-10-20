/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.powerSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.toSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.ofSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.equivSetNat
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.succSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.predSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.succMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.predMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.unionMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.interMap₂
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.mem_powerSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.powerSet_master
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.powerSet_inter_mem
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.mem_compl_singleton
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.mem_toSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.mem_compl_of_finite
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.toSet_ofSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.ofSet_toSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.ofSet_mono
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.mem_predSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.succSet_mono
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.predSet_mono

@[expose] public section

/-!
# Exercise 2.20 (Scott 1981, PRG-19, §2) — the powerset domain `𝒫`

> **EXERCISE 2.20.** Discuss again the example of Exercise 1.15 where the domain turns out to be the
> powerset of `ℕ`. Show how the finite elements can be taken to be the finite subsets of `ℕ` and can
> be identified with the tokens of a suitable neighbourhood system `𝒫`. (Hint: Define `↑F` for finite
> sets `F ⊆ ℕ`.) Show that both `x ∪ y` and `x ∩ y` are approximable functions of two variables, and
> that `x + 1 = {n + 1 ∣ n ∈ x}` and `x − 1 = {n ∣ n + 1 ∈ x}` are approximable.

> ⚠ **Numbering note.** Our `Exercise115.lean` formalized the *flat*/*stem* systems, **not** the
> powerset domain; so `𝒫` is built fresh here.

**Token encoding.** We take tokens `Δ = ℕ` and let the neighbourhoods of `𝒫` be the **cofinite**
subsets of `ℕ`. Since the principal-filter map `X ↦ ↑X` is inclusion-*reversing*, the finite element
`↑X` represents the finite set `Xᶜ`; as `Xᶜ` grows (more elements known to be *in* the set), the
neighbourhood `X` shrinks (more information). Concretely a finite subset `F ⊆ ℕ` is the finite
element `↑(Fᶜ)`, and `⊥ = ↑ℕ` is the empty set.

* `powerSet : NeighborhoodSystem ℕ` — cofinite sets (closed under finite `∩`).
* `toSet x := {n ∣ {n}ᶜ ∈ x}` and `ofSet S` — the identification, packaged as
  **`equivSetNat : |𝒫| ≃o (Set ℕ, ⊆)`** (`toSet`/`ofSet` mutually inverse, order-iso).
* `unionMap`, `interMap₂ : ApproximableMap₂ 𝒫 𝒫 𝒫` — `x ∪ y`, `x ∩ y` (Exercise 2.19), with
  `toSet_unionMap`/`toSet_interMap₂` proving the elementwise action is `∪`/`∩` on `Set ℕ`.
* `succMap`, `predMap : ApproximableMap 𝒫 𝒫` — `x + 1`, `x − 1`, with `toSet_succMap`/`toSet_predMap`.

Choice-free (`#print axioms ⊆ {propext, Quot.sound}`); the `Set.Finite.induction_on` in
`mem_compl_of_finite` is structural recursion on a finiteness proof, not `Classical.choice`. -/

namespace DomainTheory.NeighbourhoodSystems.Exercise220

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-! ### The neighbourhood system `𝒫` (cofinite sets). -/





/-! ### The identification `|𝒫| ≃o Set ℕ`. -/









/-! ### The shift maps `x + 1` and `x − 1`. -/






/-! ### Union and intersection as two-variable approximable maps. -/


end DomainTheory.NeighbourhoodSystems.Exercise220

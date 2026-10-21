/-ai
This file gathers and re-exports the function space and the single-step ingredients of Scott's Exercise 3.21: the least map of one step, the output intersection for an input contained in the step input and for an input not contained in it, and consistency of a single step.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise321.leastStep
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise321.interYs_single_subset_eq
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise321.interYs_single_not_subset_eq
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise321.stepCons

@[expose] public section

/-!
# Exercise 3.21 (Scott 1981, PRG-19, §3) — when does `[Y, Z]` determine `Y` and `Z`?

In the proof of Theorem 3.12 it is tacitly assumed that the function-space neighbourhood `[Y, Z]`
(the set `step Y Z = {f ∣ Y f Z}` of approximable mappings) uniquely determines its endpoints `Y`, `Z`.
Scott's Exercise 3.21 asks to make this precise.

* **If `Z ≠ Δ₂`** the pair is determined: `[Y, Z] = [Y', Z']` forces `Y = Y'` and `Z = Z'`
  (`step_eq_of_ne_master`). The hint is to use the *least* element of `[Y, Z]` — here the single-step
  map `leastMap [(Y, Z)]` of Proposition 3.9.
* **If `Z = Δ₂`** then `[Y, Δ₂] = |𝒟₁ → 𝒟₂|` is the whole space for *every* `Y` (`step_master_right`),
  so `Y` is not determined; nevertheless the biconditional of Theorem 3.12 stays valid because
  `Δ₁ g Δ₂` always holds.
* **General criterion** (`step_eq_iff`): `[Y, Z] = [Y', Z']` iff either both outputs are `Δ₂`, or
  `Y = Y'` and `Z = Z'`.

Everything is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-! ### The intersection `interYs` of a single step. -/


/-! ### The least element of a single step neighbourhood. -/


/-! ### `[Y, Z]` is the whole space exactly when `Z = Δ₂`. -/

/-! ### Uniqueness when `Z ≠ Δ₂`. -/

/-! ### The general identity criterion. -/
end DomainTheory.NeighbourhoodSystems

/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.iterMap
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.fixElement
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.iterElem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.fixMap
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.iterMap_zero
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.iterMap_succ
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.comp_mono
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.iterMap_mono_map
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.iter_comm
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.rel_master_succ
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.rel_master_mono
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.mem_fixElement
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.fixElement_mono

@[expose] public section

/-!
# Lecture IV (§4) — fixed points and recursion: Theorems 4.1 and 4.2

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19 (1981), Lecture IV,
*Fixed points and recursion*. The heart of the matter is the **Fixed-point Theorem**:

* **Theorem 4.1** — every approximable mapping `f : 𝒟 → 𝒟` has a *least* element `x ∈ |𝒟|` with
  `f(x) = x`. Scott constructs `x = {X ∈ 𝒟 ∣ Δ fⁿ X for some n}`, the family of neighbourhoods
  reachable from the master `Δ` along finitely many `f`-steps. We model the `n`-fold composition
  `fⁿ` by `iterMap f n` (`f⁰ = I_𝒟`, `f^{n+1} = f ∘ fⁿ`) and the fixed point by `fixElement f`.
  The fixed-point equation is `toElementMap_fixElement`; minimality among *pre-fixed* points
  (`f(z) ⊆ z ⟹ x ⊆ z`) is `fixElement_le_of_toElementMap_le`.

* **Theorem 4.2** — the operator `fix : (𝒟 → 𝒟) → 𝒟` is itself approximable. We build it as
  `fixMap V : ApproximableMap (funSpace V V) V` via the extension-from-finite-elements principle
  (Exercise 2.8, `ofMono`), sending the finite element `↑F` to `fix(↑F)` where `↑F = leastMap` is
  the least map of the neighbourhood `F` (here `toApproxMap (↑F)`). The defining computation
  `fixMap.toElementMap φ = fix(toApproxMap φ)` is Scott's equation (∗)
  `fix(f) = ⋃ {fix(↑F) ∣ f ∈ [F]}` (`fixMap_toElementMap`), whose non-trivial half — every
  finite `f`-chain factors through one finite approximant `F ∈ φ` — is `exists_principal_iterMap`.
  Then (i) `fix(f) = f(fix(f))` (`fixMap_fixed`); (ii) `f(x) ⊆ x ⟹ fix(f) ⊆ x` (`fixMap_least`);
  (iii) `fix(f) = ⊔ₙ fⁿ(⊥)` (`fixMap_eq_iSup`, with `iterElem_eq_iterate` giving the faithful
  `⊔ₙ fⁿ(⊥)` form); and uniqueness (`fixMap_unique`).

All *data* constructions (`iterMap`, `fixElement`, `iterElem`, `fixMap`) are **choice-free**
(`#print axioms ⊆ {propext, Quot.sound}`); the uniqueness lemma `fixMap_unique` pulls
`Classical.choice` only through the project's `ext_of_toElementMap`, as permitted.
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-! ### The iterated map `fⁿ`. -/









/-! ### Theorem 4.1 — the least fixed point. -/




/-! ### Theorem 4.2(iii) — the iterates `fⁿ(⊥)`. -/


end ApproximableMap

/-! ### Theorem 4.2 — the approximable fixed-point operator `fix`. -/

open ApproximableMap

end DomainTheory.NeighbourhoodSystems

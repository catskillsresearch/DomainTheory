/-ai
This file gathers and re-exports the generating operator, the carved-out set, the zero and successor of its subtype, the Peano structure on that subtype, the standard Peano model on the naturals, membership of zero and of successors, induction for the carved-out set, and the subtype abbreviation. The module comment records Scott's claim that a structured set in which zero is never a successor and successor is injective contains a subset satisfying those two laws together with induction, namely the least fixed point of the operator adjoining zero and closing under successor, and that the standard naturals witness the existence of such a partial model.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem46
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise422.genOp
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise422.nats
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise422.subZero
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise422.subSucc
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise422.peanoSub
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise422.natPeano
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise422.zero_mem_nats
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise422.succ_mem_nats
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise422.nats_induction
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise422.Nat'

@[expose] public section

/-!
# Exercise 4.22 (Scott 1981, PRG-19, Lecture IV) — carving a Peano model out of a partial one

Suppose `N*` is a structured set `⟨N*, 0, ⁺⟩` satisfying **only** axioms (i) and (ii) of
Definition 4.5 — i.e. `0 ≠ n⁺` (zero is not a successor) and `⁺` is injective — but *not necessarily*
the induction axiom (iii). **Must there be a subset `N ⊆ N*` that satisfies (i), (ii), and (iii)?**

**Yes.** Following Scott's hint, take the **least fixed point in `P(N*)`** (Exercise 4.14 / 4.13(2),
the dual Knaster–Tarski over the complete lattice `P(N*)`) of the monotone operator

  `g(x) = {0} ∪ x⁺ = {0} ∪ {n⁺ ∣ n ∈ x}`.

This least fixed point `nats` is the smallest subset of `N*` containing `0` and closed under `⁺`
(`zero_mem_nats`, `succ_mem_nats`). On the subtype `N = {m // m ∈ nats}`:

* (i) `0 ≠ n⁺` and (ii) `⁺` injective are **inherited** from `N*`;
* (iii) **induction** holds *by minimality* of the least fixed point: a subset of `N` closed under
  `0`/`⁺` pulls back to a pre-fixed point of `g` in `P(N*)`, which therefore contains `nats`.

So `⟨N, 0, ⁺⟩` is a genuine model of Peano's Axioms (`peanoSub`), giving
`exists_peano_submodel`.

*(For set theorists.)* The existence of such an `N*` at all is guaranteed by the **axiom of
infinity**: the standard `⟨ℕ, 0, ⁺⟩` is one (`PeanoModel ℕ`, recorded as `natPeano`), and indeed it
already satisfies (iii), so it is its own carved-out model.

The subset `nats` is built choice-free (`lfpSet`); the `PeanoModel` packaging of `peanoSub` and the
existence statement live over `Classical.choice` exactly as Theorem 4.6's bijection does.
-/

namespace DomainTheory.NeighbourhoodSystems.Exercise422

open DomainTheory.NeighbourhoodSystems DomainTheory.NeighbourhoodSystems.Exercise414

variable {M : Type*} (zero : M) (succ : M → M)


/-! ### The carved-out structure is a model of Peano's Axioms. -/


/-! ### Existence of `N*` (axiom of infinity): the standard `ℕ`. -/

end DomainTheory.NeighbourhoodSystems.Exercise422

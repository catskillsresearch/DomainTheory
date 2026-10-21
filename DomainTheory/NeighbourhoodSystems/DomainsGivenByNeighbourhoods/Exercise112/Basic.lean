/-ai
A set belongs to the limit element of the final-segment system if and only if it is a neighbourhood of that system.

The two sides are definitionally the same.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise112.tail
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise112.mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise112.neighborhoodSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise112.fin
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise112.top
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise112.mem_tail
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise112.tail_subset_iff
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise112.tail_inter
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise112.nestedOrDisjoint
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise112.ns_mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise112.mem_tail_nbhd

@[expose] public section

/-!
# Exercise 1.12 (Scott 1981, PRG-19, §1) — the final-segment system on `ℕ`

Let `Δ = ℕ` and take as neighbourhoods the **final segments** (tails)

`tail n = {m ∈ ℕ ∣ n ≤ m}`,

so `tail 0 = ℕ = Δ` and `tail 0 ⊇ tail 1 ⊇ tail 2 ⊇ ⋯` is a descending chain (Scott's `{m ∣ m > n}`
is `tail (n+1)`). This generalizes Example 1.3 (a *chain*) to the countably infinite case.

Deliverables:

* `neighborhoodSystem : NeighborhoodSystem ℕ` (the tails are pairwise nested, so Factoid 1.4a
  applies) — verifies it is a neighbourhood system.
* **Finite elements.** `fin n = ↑(tail n)`, the principal filters; they form an ascending `ω`-chain
  `fin 0 ⊏ fin 1 ⊏ ⋯` (`fin_le_iff`, `fin_strictMono`).
* **The limit / total element.** `top = 𝒟` itself (all tails) is the greatest element (`le_top`),
  is the *unique* total (maximal) element (`top_isTotal`, `isTotal_iff_top`).
* **Classification** (the "only one limit element" hint): every element is either a finite `fin n`
  or the limit `top` (`element_eq`). This single result is *classical* (it decides whether the set
  of indices in `x` is bounded — `Nat.find` over a `¬`-predicate); everything else is constructive.
-/

namespace DomainTheory.NeighbourhoodSystems.Exercise112

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


/-! ### Finite elements: the principal filters `fin n = ↑(tail n)`. -/


/-! ### The limit element: the whole system `𝒟`, the greatest / unique total element. -/


@[simp] theorem mem_top {X : Set ℕ} : top.mem X ↔ neighborhoodSystem.mem X := Iff.rfl

/-! ### Classification: finite `fin n`, or the limit `top` (classical). -/
end DomainTheory.NeighbourhoodSystems.Exercise112

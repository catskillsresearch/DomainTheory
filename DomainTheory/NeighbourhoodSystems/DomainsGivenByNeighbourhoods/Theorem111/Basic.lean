module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Order.Monotone.Basic
import all Mathlib.Order.Monotone.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem111.iInter
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem111.iUnion
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem111.mem_iInter

@[expose] public section

/-!
# Theorem 1.11 (Scott 1981, PRG-19, §1) — closure of `|𝒟|` under sequential `⋂` and ascending `⋃`

If `𝒟` is a neighbourhood system and `xₙ ∈ |𝒟|` for `n = 0, 1, 2, …`, then

* (i)  `⋂ₙ xₙ ∈ |𝒟|`;
* (ii) `⋃ₙ xₙ ∈ |𝒟|`, **provided** `x₀ ⊆ x₁ ⊆ x₂ ⊆ ⋯` (an ascending chain).

We realize each as a concrete `Element`:

* `iInter x` has membership `X ∈ ⋂ₙ xₙ ⟺ ∀ n, X ∈ xₙ`. All four filter laws are pointwise. It is
  the **greatest lower bound** (`iInter_le`, `le_iInter`): Scott's "best element that approximates
  all of the `xₙ`; exactly what is common to all".
* `iUnion x hmono` (with `hmono : Monotone x`) has `X ∈ ⋃ₙ xₙ ⟺ ∃ n, X ∈ xₙ`. Only filter law (ii)
  (closure under `∩`) needs the proviso: from `X ∈ xₙ`, `Y ∈ xₘ` take `k = max n m`, where
  monotonicity puts both `X, Y ∈ x_k`, so `X ∩ Y ∈ x_k`. It is the **least upper bound**
  (`le_iUnion`, `iUnion_le`): "just what the increasing sequence approximates".

Everything is constructive (`[propext, Quot.sound]`).
-/

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-! ### (i) Countable intersection. -/



/-! ### (ii) Ascending countable union. -/


@[simp] theorem mem_iUnion (x : ℕ → V.Element) (hmono : Monotone x) {X : Set α} :
    (V.iUnion x hmono).mem X ↔ ∃ n, (x n).mem X := Iff.rfl
end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems

module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Basic.Real.Basic
import all Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
import all Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import all Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise117.ratIntervalMem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise117.ratIntervalSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise117.filterAt
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise117.ratIntervalMem_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise117.inter_mem'
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise117.ratIntervalSystem_mem

@[expose] public section

/-!
# Exercise 1.17 (Scott 1981, PRG-19, §1) — rational open intervals on `ℝ`

`Δ = ℝ`; `𝒟 =` the non-empty open intervals with rational endpoints, plus `Δ` itself
(`ratIntervalSystem`). The system law (`inter_mem`) reduces to the fact that the intersection of
two rational intervals is empty or again a rational interval
(`Set.Ioo_inter_Ioo` with `max`/`min` of the rational endpoints): `inter_mem'`.

For each real `t`, `filterAt t = {X ∈ 𝒟 ∣ t ∈ X}` is a filter (`filterAt`). These embed `ℝ` into
`|𝒟|` injectively (`filterAt_injective`, using rational density), so `|𝒟|` contains a faithful
copy of the reals.

**Scope.** Scott's full classification of the *total* elements (the hint: for rational `t`,
intervals with `t` as a right-hand endpoint give a *second* total element at `t`) needs more
real analysis and is left to prose; we deliver the system, the point-filters, and their
injectivity. This is the first **uncountable** `Δ` of the block.

The constructions are `[propext, Quot.sound]`; injectivity uses `exists_rat_btwn` (Archimedean,
classical).
-/

namespace DomainTheory.NeighbourhoodSystems

namespace RatInterval

open NeighborhoodSystem







@[simp] theorem mem_filterAt {t : ℝ} {X : Set ℝ} :
    (filterAt t).mem X ↔ ratIntervalMem X ∧ t ∈ X := Iff.rfl
end RatInterval
end DomainTheory.NeighbourhoodSystems

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
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise117.ratIntervalMem_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise117.inter_mem'

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace RatInterval

open NeighborhoodSystem

/-- **Exercise 1.17 — the rational-interval neighbourhood system over `ℝ`.** -/
def ratIntervalSystem : NeighborhoodSystem ℝ where
  mem := ratIntervalMem
  master := Set.univ
  master_nonempty := Set.univ_nonempty
  master_mem := Or.inl rfl
  inter_mem := by
    intro X Y Z hX hY hZ hZsub
    exact inter_mem' hX hY ((ratIntervalMem_nonempty hZ).mono hZsub)
  sub_master := fun _ => Set.subset_univ _

end RatInterval

end DomainTheory.NeighbourhoodSystems

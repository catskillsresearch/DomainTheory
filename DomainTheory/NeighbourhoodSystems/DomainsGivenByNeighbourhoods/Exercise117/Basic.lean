module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise117.ratIntervalMem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise117.ratIntervalSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise117.filterAt
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise117.ratIntervalMem_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise117.inter_mem'
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise117.ratIntervalSystem_mem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace RatInterval

open NeighborhoodSystem


@[simp] theorem mem_filterAt {t : ℝ} {X : Set ℝ} :
    (filterAt t).mem X ↔ ratIntervalMem X ∧ t ∈ X := Iff.rfl
end RatInterval
end DomainTheory.NeighbourhoodSystems

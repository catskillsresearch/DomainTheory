/-ai
The neighbourhood system of all subsets of the natural numbers declares every set to be a neighbourhood, with the whole set as master neighbourhood. The master is nonempty. Membership of the master and closure under intersection hold outright, and every set is contained in the master.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.cofiniteSystem_mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.mem_ofExcluded
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.mem_toExcluded

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Cofinite

open NeighborhoodSystem

/-- **Exercise 1.16 (second example).** All subsets of `ℕ` form a neighbourhood system, trivially
closed under *all* finite intersections. Unlike `cofiniteSystem` it is **not** positive (`∅` is a
neighbourhood). Every neighbourhood is a finite element via `principal`; its total elements are
the principal filters of singletons (the system is "flat"). -/
def fullSystem : NeighborhoodSystem ℕ where
  mem _ := True
  master := Set.univ
  master_nonempty := Set.univ_nonempty
  master_mem := trivial
  inter_mem := fun _ _ _ _ => trivial
  sub_master := fun _ => Set.subset_univ _

end Cofinite

end DomainTheory.NeighbourhoodSystems

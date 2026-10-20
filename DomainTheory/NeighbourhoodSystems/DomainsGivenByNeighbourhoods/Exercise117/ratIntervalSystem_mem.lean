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

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace RatInterval

open NeighborhoodSystem

@[simp] theorem ratIntervalSystem_mem {X : Set ℝ} :
    ratIntervalSystem.mem X ↔ ratIntervalMem X := Iff.rfl

end RatInterval

end DomainTheory.NeighbourhoodSystems

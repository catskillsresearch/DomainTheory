/-ai
A set belongs to the cofinite neighbourhood system exactly when its complement is finite.

The two sides are definitionally identical.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.cofiniteSystem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Cofinite

open NeighborhoodSystem

@[simp] theorem cofiniteSystem_mem {X : Set ℕ} : cofiniteSystem.mem X ↔ Xᶜ.Finite := Iff.rfl

end Cofinite

end DomainTheory.NeighbourhoodSystems

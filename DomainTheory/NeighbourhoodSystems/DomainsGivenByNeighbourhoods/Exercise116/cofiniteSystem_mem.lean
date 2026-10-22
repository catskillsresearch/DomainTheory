module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.cofiniteSystem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Cofinite

open NeighborhoodSystem

@[simp] theorem cofiniteSystem_mem {X : Set ℕ} : cofiniteSystem.mem X ↔ Xᶜ.Finite := Iff.rfl

end Cofinite

end DomainTheory.NeighbourhoodSystems

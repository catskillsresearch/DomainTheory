module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Order.Monotone.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem111.iInter
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem111.iUnion
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem111.mem_iInter

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


@[simp] theorem mem_iUnion (x : ℕ → V.Element) (hmono : Monotone x) {X : Set α} :
    (V.iUnion x hmono).mem X ↔ ∃ n, (x n).mem X := Iff.rfl
end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems

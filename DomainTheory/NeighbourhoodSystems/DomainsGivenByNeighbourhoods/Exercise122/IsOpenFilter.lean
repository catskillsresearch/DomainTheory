/-ai
A set of elements is an open filter when every element of the set contains a neighbourhood whose basic open is contained in the set.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Topology.Inseparable
import all Mathlib.Topology.Inseparable
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise122.basicOpen
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise122.mem_basicOpen

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- A set `𝒰 ⊆ |𝒟|` is *open* (Exercise 1.22, condition (ii)) when every point `x ∈ 𝒰` has a
basic neighbourhood `[X]` with `X ∈ x` contained in `𝒰`. -/
def IsOpenFilter (U : Set V.Element) : Prop :=
  ∀ x ∈ U, ∃ X, x.mem X ∧ V.basicOpen X ⊆ U

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems

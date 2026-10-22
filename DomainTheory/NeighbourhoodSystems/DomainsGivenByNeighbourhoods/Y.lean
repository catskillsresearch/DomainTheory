module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.state

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise123

open NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α) (enum : ℕ → Set α) [DecidablePred V.mem]

/-- The greedy sequence `Yₙ = (state n).1`. -/
def Y (n : ℕ) : Set α := (state V enum n).1

end Exercise123

end DomainTheory.NeighbourhoodSystems

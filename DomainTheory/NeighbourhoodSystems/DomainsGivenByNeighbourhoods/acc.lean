/-ai
The running intersection at stage n is the second component of the state at that stage.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.state

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise123

open NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α) (enum : ℕ → Set α) [DecidablePred V.mem]

/-- The running intersection `acc n = ⋂_{i≤n} Yᵢ = (state n).2`. -/
def acc (n : ℕ) : Set α := (state V enum n).2

end Exercise123

end DomainTheory.NeighbourhoodSystems

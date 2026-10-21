/-ai
At a successor, the greedy state is the next enumerated set paired with its intersection against the running intersection when the consistency test holds, and is the previous state otherwise.

The two sides agree by reflexivity.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.state
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.acc
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.cond
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Y_zero
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.acc_zero

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise123

open NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α) (enum : ℕ → Set α) [DecidablePred V.mem]

/-- The defining equation of `state` at a successor, written with the named `cond`/`acc`. -/
theorem state_succ (n : ℕ) :
    state V enum (n + 1) =
      if cond V enum n then (enum (n + 1), acc V enum n ∩ enum (n + 1)) else state V enum n :=
  rfl

end Exercise123

end DomainTheory.NeighbourhoodSystems

/-ai
If the condition fails at stage n, the greedy sequence at the next stage equals the greedy sequence at stage n.

Unfold both sides as first components of states, rewrite the successor state, and take the right branch of the conditional.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.state
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Y
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.cond
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Y_zero
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.acc_zero
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.state_succ

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise123

open NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α) (enum : ℕ → Set α) [DecidablePred V.mem]

theorem Y_succ_neg {n : ℕ} (h : ¬ cond V enum n) : Y V enum (n + 1) = Y V enum n := by
  show (state V enum (n + 1)).1 = (state V enum n).1
  rw [state_succ, ite_eq_right h]

end Exercise123

end DomainTheory.NeighbourhoodSystems

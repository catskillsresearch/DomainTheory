/-ai
If the consistency test holds at stage n, the running intersection at n + 1 equals the running intersection at n met with the next enumerated set.

The left side is the second component of the greedy state at n + 1. The successor equation of the state is rewritten, and the conditional takes its left branch because the test holds.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.state
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.acc
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.cond
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Y_zero
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.acc_zero
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.state_succ

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise123

open NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α) (enum : ℕ → Set α) [DecidablePred V.mem]

theorem acc_succ_pos {n : ℕ} (h : cond V enum n) :
    acc V enum (n + 1) = acc V enum n ∩ enum (n + 1) := by
  show (state V enum (n + 1)).2 = acc V enum n ∩ enum (n + 1)
  rw [state_succ, ite_eq_left h]

end Exercise123

end DomainTheory.NeighbourhoodSystems

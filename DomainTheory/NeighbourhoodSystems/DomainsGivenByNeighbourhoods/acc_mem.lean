module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.acc
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.cond
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Y_zero
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.acc_zero
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.acc_succ_pos
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.acc_succ_neg

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise123

open NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α) (enum : ℕ → Set α) [DecidablePred V.mem]

variable (henum : ∀ n, V.mem (enum n))

include henum

/-- The running intersection `acc n` is always a neighbourhood — the greedy choice guarantees it.
This is the content of Scott's hint (consistency of the prefix). -/
theorem acc_mem : ∀ n, V.mem (acc V enum n) := by
  intro n
  induction n with
  | zero =>
    rw [acc_zero, Set.inter_eq_right.mpr (V.sub_master (henum 0))]
    exact henum 0
  | succ n ih =>
    by_cases h : cond V enum n
    · rw [acc_succ_pos V enum h]; exact h
    · rw [acc_succ_neg V enum h]; exact ih

end Exercise123

end DomainTheory.NeighbourhoodSystems

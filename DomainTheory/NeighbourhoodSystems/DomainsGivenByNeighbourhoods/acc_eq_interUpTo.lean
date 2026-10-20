module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Y
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.acc
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.cond
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Y_zero
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.acc_zero
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Y_succ_pos
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Y_succ_neg
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.acc_succ_pos
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.acc_succ_neg

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise123

open NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α) (enum : ℕ → Set α) [DecidablePred V.mem]

/-- `acc n = ⋂_{i<n+1} Yᵢ`: the carried intersection is exactly the prefix intersection. -/
theorem acc_eq_interUpTo : ∀ n, acc V enum n = V.interUpTo (Y V enum) (n + 1) := by
  intro n
  induction n with
  | zero =>
    rw [acc_zero, interUpTo_succ, interUpTo_zero, Y_zero]
  | succ n ih =>
    rw [interUpTo_succ, ← ih]
    by_cases h : cond V enum n
    · rw [acc_succ_pos V enum h, Y_succ_pos V enum h]
    · rw [acc_succ_neg V enum h, Y_succ_neg V enum h]
      have hsub : acc V enum n ⊆ Y V enum n := by
        rw [ih]; exact V.interUpTo_subset (Y V enum) (Nat.lt_succ_self n)
      rw [Set.inter_eq_left.mpr hsub]

end Exercise123

end DomainTheory.NeighbourhoodSystems

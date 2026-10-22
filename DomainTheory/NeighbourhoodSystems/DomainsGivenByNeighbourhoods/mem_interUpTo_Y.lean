module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Y
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Y_zero
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.acc_zero
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.acc_eq_interUpTo
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.acc_mem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise123

open NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α) (enum : ℕ → Set α) [DecidablePred V.mem]

variable (henum : ∀ n, V.mem (enum n))

include henum

/-- `⋂_{i<n} Yᵢ` is always a neighbourhood. -/
theorem mem_interUpTo_Y : ∀ n, V.mem (V.interUpTo (Y V enum) n) := by
  intro n
  cases n with
  | zero => rw [interUpTo_zero]; exact V.master_mem
  | succ n => rw [← acc_eq_interUpTo V enum]; exact acc_mem V enum henum n

end Exercise123

end DomainTheory.NeighbourhoodSystems

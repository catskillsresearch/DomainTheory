/-ai
The running intersection at stage 0 is the master neighbourhood met with the first enumerated set.

The two sides agree by reflexivity.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.acc
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Y_zero

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise123

open NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α) (enum : ℕ → Set α) [DecidablePred V.mem]

@[simp] theorem acc_zero : acc V enum 0 = V.master ∩ enum 0 := rfl

end Exercise123

end DomainTheory.NeighbourhoodSystems

/-ai
A set W belongs to the empty finite join if and only if W is the master neighbourhood of the power domain.

Rewrite the empty join as the bottom element and rewrite bottom membership by the identification of the power-domain master.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition711.PDfinJoinZero

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

@[simp] theorem PDmem_finJoinZero {W : Set (Set α)} :
    (V.PDfinJoinZero).mem W ↔ W = V.PowerDomain.master := by
  rw [PDfinJoinZero, mem_bot, PowerDomain_master]

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems

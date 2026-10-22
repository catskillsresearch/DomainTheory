module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition711.PDfinJoinZero

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

@[simp] theorem PDmem_finJoinZero {W : Set (Set α)} :
    (V.PDfinJoinZero).mem W ↔ W = V.PowerDomain.master := by
  rw [PDfinJoinZero, mem_bot, PowerDomain_master]

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems

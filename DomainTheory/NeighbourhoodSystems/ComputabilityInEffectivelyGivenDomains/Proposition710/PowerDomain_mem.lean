/-ai
A set of sets is a neighbourhood of the Smyth power domain if and only if it is a power-domain neighbourhood.

The two sides are the same by the definition.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

@[simp] theorem PowerDomain_mem {W : Set (Set α)} : V.PowerDomain.mem W ↔ V.PDmem W := Iff.rfl

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems

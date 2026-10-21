/-ai
A set lies in the finite union of the down-sets of a list of codes if and only if it lies in the down-set of the enumerated neighbourhood of some code in the list.

This is the membership rule for an indexed union.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.UPX

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

variable (P : ComputablePresentation V)

theorem mem_UPX {l : List ℕ} {z : Set α} :
    z ∈ V.UPX P l ↔ ∃ b ∈ l, z ∈ V.upSet (P.X b) := by
  simp only [UPX, Set.mem_iUnion, exists_prop]

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems

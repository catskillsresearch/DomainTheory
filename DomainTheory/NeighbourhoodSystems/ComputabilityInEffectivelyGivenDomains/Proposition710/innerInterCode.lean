/-ai
The inner intersection code of an outer index a, an accumulator, and a code m is the fold of the inner intersection step along m, starting from that accumulator, with parameter a.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.innerInterStp

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

variable (P : ComputablePresentation V)

/-- The inner fold: process `decodeList m`, accumulating the consistent intersection indices. -/
def innerInterCode (cons : ℕ → ℕ) (a acc m : ℕ) : ℕ := foldCode (V.innerInterStp P cons) a acc m

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems

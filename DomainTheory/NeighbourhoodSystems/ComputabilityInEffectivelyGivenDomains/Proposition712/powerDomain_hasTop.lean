/-ai
The element lattice of a power domain always has a greatest element.

The power domain is unconditionally closed under intersection, so the theorem on intersection-closed systems applies.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition711
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.hasTop_of_inter_closed

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive


namespace Counterexample712C

open NeighborhoodSystem

variable {γ δ : Type*}


/-- **`ℙ𝒟` is unconditionally closed under intersection** (`PDmem_inter`; the empty union always
supplies the consistency witness). Hence `|ℙ𝒟|` always has a greatest element. -/
theorem powerDomain_hasTop (V : NeighborhoodSystem γ) : HasTop V.PowerDomain :=
  hasTop_of_inter_closed V.PowerDomain (fun hX hY => V.PDmem_inter hX hY)

end Counterexample712C
end DomainTheory.NeighbourhoodSystems

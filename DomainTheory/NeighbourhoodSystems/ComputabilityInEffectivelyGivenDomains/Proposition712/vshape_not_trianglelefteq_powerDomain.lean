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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.hasTop_of_trianglelefteq_powerDomain
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.Vshape_not_hasTop

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive


namespace Counterexample712C

open NeighborhoodSystem

variable {γ δ : Type*}


/-- **Proposition 7.12, Part C is FALSE in general.** The flat two-point domain `Vshape` is *not* a
subdomain of its own Smyth power domain: `Vshape ⋬ ℙ(Vshape)`. (Contrast Parts A, B, D, which hold
for every `𝒟`.) -/
theorem vshape_not_trianglelefteq_powerDomain : ¬ (Vshape ⊴ Vshape.PowerDomain) := fun h =>
  Vshape_not_hasTop (hasTop_of_trianglelefteq_powerDomain h)

end Counterexample712C
end DomainTheory.NeighbourhoodSystems

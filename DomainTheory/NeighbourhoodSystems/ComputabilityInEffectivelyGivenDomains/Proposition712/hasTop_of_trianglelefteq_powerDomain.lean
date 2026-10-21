/-ai
If a neighbourhood system is a subdomain of the power domain of another system, then it has a greatest element.

The subdomain relation supplies a subsystem of the power domain and an order isomorphism with that subsystem. The power domain is closed under intersection. The subsystem inherits that closure, hence has a greatest element, and the isomorphism transports the greatest element back.
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
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.hasTop_of_inter_closed
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.subsystem_inter_closed
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.hasTop_of_iso

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive



namespace Counterexample712C

open NeighborhoodSystem

variable {γ δ : Type*}



/-- **`D ⊴ ℙ𝒟` forces `|D|` to have a greatest element.** This is the obstruction behind Part C. -/
theorem hasTop_of_trianglelefteq_powerDomain {D : NeighborhoodSystem γ} {E : NeighborhoodSystem δ}
    (h : D ⊴ E.PowerDomain) : HasTop D := by
  obtain ⟨D', hsub, ⟨e⟩⟩ := h
  have hPcl : ∀ {X Y : Set (Set δ)}, E.PowerDomain.mem X → E.PowerDomain.mem Y →
      E.PowerDomain.mem (X ∩ Y) := fun hX hY => E.PDmem_inter hX hY
  exact hasTop_of_iso e (hasTop_of_inter_closed D' (subsystem_inter_closed hsub hPcl))

end Counterexample712C
end DomainTheory.NeighbourhoodSystems

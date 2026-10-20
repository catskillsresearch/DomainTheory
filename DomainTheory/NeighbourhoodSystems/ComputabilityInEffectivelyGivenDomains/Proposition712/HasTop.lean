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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.PDsingletonApproxMap_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.PDsingletonMeet_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.finJoinMap_prod_rel

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive

namespace Counterexample712C

open NeighborhoodSystem

variable {γ δ : Type*}

/-- A domain *has a greatest element* if some element dominates every other. Order-isomorphisms and
the inclusion order on filters transport this property. -/
def HasTop (E : NeighborhoodSystem γ) : Prop := ∃ t : E.Element, ∀ x : E.Element, x ≤ t

end Counterexample712C

end DomainTheory.NeighbourhoodSystems

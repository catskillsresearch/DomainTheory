/-ai
The empty set is not a neighbourhood of the flat two-point domain.

Membership is the full set, the singleton of true, or the singleton of false, and the empty set equals none of these.
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

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive



namespace Counterexample712C

open NeighborhoodSystem

variable {γ δ : Type*}







/-- `∅` is not a `Vshape`-neighbourhood (each neighbourhood is nonempty). -/
theorem Vshape_not_mem_empty : ¬ Vshape.mem (∅ : Set Bool) := by
  rintro (h | h | h)
  · exact Set.empty_ne_univ h
  · exact absurd h.symm (Set.singleton_ne_empty true)
  · exact absurd h.symm (Set.singleton_ne_empty false)

end Counterexample712C
end DomainTheory.NeighbourhoodSystems

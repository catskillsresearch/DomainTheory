/-ai
The binary join relates X and Y to W if and only if both singleton maps relate their argument to W.

The two sides are definitionally equal.
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

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


variable (P : ComputablePresentation V)

/-- **Proposition 7.12 — binary join reduces to two singleton tests.** -/
theorem PDfinJoinApproxMap₂_rel_iff {X Y : Set α} (_hX : V.mem X) (_hY : V.mem Y) {W : Set (Set α)} :
    (PDfinJoinApproxMap₂ (V := V)).rel X Y W ↔
      (PDsingletonApproxMap (V := V)).rel X W ∧ (PDsingletonApproxMap (V := V)).rel Y W := Iff.rfl

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems

/-ai
The singleton map relates a neighbourhood X to a power-domain neighbourhood W if and only if the singleton of the principal element of X contains W.

Unfold the map as the monotone extension. A related pair supplies membership in that singleton, and conversely that membership is the relation at the given neighbourhood X.
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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.PDsingletonApproxMap

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

@[simp] theorem PDsingletonApproxMap_rel {X : Set α} {W : Set (Set α)} (hX : V.mem X) :
    (PDsingletonApproxMap (V := V)).rel X W ↔ (V.PDsingleton (V.principal hX)).mem W := by
  dsimp [PDsingletonApproxMap, ofMono]
  constructor
  · intro ⟨_, h⟩; exact h
  · intro h; exact ⟨hX, h⟩

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems

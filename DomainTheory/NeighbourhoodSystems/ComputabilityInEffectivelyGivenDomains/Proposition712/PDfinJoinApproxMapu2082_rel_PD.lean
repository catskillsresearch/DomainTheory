/-ai
The binary join relates neighbourhoods X and Y to a power-domain neighbourhood W if and only if the binary finite join of the two principal elements contains W.

The relation is the conjunction of the two singleton relations. Each singleton relation is membership of W in the singleton of the corresponding principal element, and the binary intersection law says that the join contains W if and only if both singletons do. Both directions rewrite by these two facts.
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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.PDfinJoin_inter_two

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)













variable (P : ComputablePresentation V)

theorem PDfinJoinApproxMap₂_rel_PD {X Y : Set α} (hX : V.mem X) (hY : V.mem Y) {W : Set (Set α)} :
    (PDfinJoinApproxMap₂ (V := V)).rel X Y W ↔
      (V.PDfinJoin 2 ![V.principal hX, V.principal hY]).mem W := by
  constructor
  · intro ⟨h1, h2⟩
    rw [PDsingletonApproxMap_rel (hX := hX)] at h1
    rw [PDsingletonApproxMap_rel (hX := hY)] at h2
    exact (PDfinJoin_inter_two (x := V.principal hX) (y := V.principal hY)).2 ⟨h1, h2⟩
  · intro h
    rcases (PDfinJoin_inter_two (x := V.principal hX) (y := V.principal hY)).1 h with ⟨h1, h2⟩
    exact ⟨by rw [PDsingletonApproxMap_rel (hX := hX)]; exact h1,
      by rw [PDsingletonApproxMap_rel (hX := hY)]; exact h2⟩

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems

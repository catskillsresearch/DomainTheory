/-ai
The binary join map sends elements x and y to the binary finite join of x and y.

By extensionality of power-domain elements, and by the membership form of the intersection law, W lies in the join if and only if it lies in both singletons. Membership in the image of the two-variable map is a neighbourhood X of x and a neighbourhood Y of y related by both singleton relations. Each singleton relation rewrites as membership in the image of the singleton map, and conversely those two memberships unpack to such neighbourhoods.
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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.PDext
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.PDsingletonApproxMap_toElementMap
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.PDfinJoin_inter_two

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)










/-- **Proposition 7.12 — binary join action.** `PDfinJoinApproxMap₂(x, y) = {x, y}`. -/
theorem PDfinJoinApproxMap₂_toElementMap (x y : V.Element) :
    (PDfinJoinApproxMap₂ (V := V)).toElementMap₂ x y = V.PDfinJoin 2 ![x, y] := by
  apply PDext
  intro W
  rw [PDfinJoin_inter_two, ApproximableMap₂.mem_toElementMap₂]
  constructor
  · rintro ⟨X, Y, hxX, hyY, ⟨h1, h2⟩⟩
    constructor
    · rw [← PDsingletonApproxMap_toElementMap (V := V)]
      exact (ApproximableMap.mem_toElementMap (PDsingletonApproxMap (V := V)) x).mpr ⟨X, hxX, h1⟩
    · rw [← PDsingletonApproxMap_toElementMap (V := V)]
      exact (ApproximableMap.mem_toElementMap (PDsingletonApproxMap (V := V)) y).mpr ⟨Y, hyY, h2⟩
  · intro ⟨h1, h2⟩
    rw [← PDsingletonApproxMap_toElementMap (V := V)] at h1 h2
    obtain ⟨X, hxX, hrelX⟩ :=
      (ApproximableMap.mem_toElementMap (PDsingletonApproxMap (V := V)) x).mp h1
    obtain ⟨Y, hyY, hrelY⟩ :=
      (ApproximableMap.mem_toElementMap (PDsingletonApproxMap (V := V)) y).mp h2
    exact ⟨X, Y, hxX, hyY, hrelX, hrelY⟩

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems

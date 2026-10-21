/-ai
The product join map sends the pair of elements x and y to the binary finite join of x and y.

The two-variable map recovered from the product map is the binary join map. Rewriting the element action through that identification and through the action of the binary join gives the binary finite join.
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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.PDfinJoinApproxMapu2082_toElementMap

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)











theorem finJoinMap_prod_toElementMap (x y : V.Element) :
    (finJoinMap_prod (V := V)).toElementMap (pair x y) = V.PDfinJoin 2 ![x, y] := by
  have hmap : toMap₂ (finJoinMap_prod (V := V)) = PDfinJoinApproxMap₂ (V := V) := toMap₂_ofMap₂ _
  rw [← toElementMap₂_toMap₂ (finJoinMap_prod (V := V)), hmap, PDfinJoinApproxMap₂_toElementMap]

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems

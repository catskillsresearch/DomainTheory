/-ai
The product join map relates the product neighbourhood of X and Y to W if and only if the two-variable binary join relates X and Y to W.

Unfold the product map as that two-variable map. The preimages of the product neighbourhood under the two inclusions are X and Y. A related pair is a product neighbourhood together with the binary relation, and conversely the product of the two given neighbourhoods supplies that witness.
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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.PDsingletonApproxMap_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.PDsingletonMeet_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.PDfinJoinApproxMap₂
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.finJoinMap_prod

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

@[simp] theorem finJoinMap_prod_rel {X Y : Set α} (hX : V.mem X) (hY : V.mem Y) {W : Set (Set α)} :
    (finJoinMap_prod (V := V)).rel (prodNbhd X Y) W ↔
      (PDfinJoinApproxMap₂ (V := V)).rel X Y W := by
  dsimp [finJoinMap_prod, ofMap₂]
  simp only [inl_preimage_prodNbhd, inr_preimage_prodNbhd]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨prod_mem_prodNbhd hX hY, h⟩⟩

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems

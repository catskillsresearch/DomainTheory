/-ai
The binary join, as a two-variable approximable map into the power domain, relates neighbourhoods X and Y to W when both singleton maps relate their argument to W. The domain, codomain, and master laws, closure under intersection on the right, and monotonicity are the corresponding laws of the singleton map, applied to each argument.
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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.PDsingletonApproxMap_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.PDsingletonMeet_mem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Proposition 7.12 — the binary join as a two-variable approximable map.** -/
def PDfinJoinApproxMap₂ : ApproximableMap₂ V V V.PowerDomain where
  rel X Y W := (PDsingletonApproxMap (V := V)).rel X W ∧ (PDsingletonApproxMap (V := V)).rel Y W
  rel_dom₀ h := (PDsingletonApproxMap (V := V)).rel_dom h.1
  rel_dom₁ h := (PDsingletonApproxMap (V := V)).rel_dom h.2
  rel_cod h := (PDsingletonApproxMap (V := V)).rel_cod h.1
  master_rel := ⟨(PDsingletonApproxMap (V := V)).master_rel, (PDsingletonApproxMap (V := V)).master_rel⟩
  inter_right := fun ⟨h1, h2⟩ ⟨h1', h2'⟩ =>
    ⟨(PDsingletonApproxMap (V := V)).inter_right h1 h1',
      (PDsingletonApproxMap (V := V)).inter_right h2 h2'⟩
  mono := fun ⟨h1, h2⟩ hXX' hYY' hWW' hX' hY' hW' =>
    ⟨(PDsingletonApproxMap (V := V)).mono h1 hXX' hWW' hX' hW',
      (PDsingletonApproxMap (V := V)).mono h2 hYY' hWW' hY' hW'⟩

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems

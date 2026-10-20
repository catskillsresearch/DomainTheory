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

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- Meet of two `{·}`-values in `|ℙ𝒟|`. -/
def PDsingletonMeet (a b : V.PowerDomain.Element) : V.PowerDomain.Element where
  mem W := a.mem W ∧ b.mem W
  sub h := a.sub h.1
  master_mem := ⟨a.master_mem, b.master_mem⟩
  inter_mem h1 h2 := ⟨a.inter_mem h1.1 h2.1, b.inter_mem h1.2 h2.2⟩
  up_mem h hW hsub := ⟨a.up_mem h.1 hW hsub, b.up_mem h.2 hW hsub⟩

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems

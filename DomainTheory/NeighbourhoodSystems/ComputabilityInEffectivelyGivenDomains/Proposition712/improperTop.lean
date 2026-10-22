/-ai
When a neighbourhood system is unconditionally closed under intersection, the family of all its neighbourhoods is an element. Subsets of members remain members, the master neighbourhood belongs to it, the intersection of two members belongs to it by the closure hypothesis, and any neighbourhood above a member is itself a member.
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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.PDsingletonApproxMap_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.PDsingletonMeet_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.finJoinMap_prod_rel

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive

namespace Counterexample712C

open NeighborhoodSystem

variable {γ δ : Type*}

/-- **The improper filter.** When a system `E` is *unconditionally* closed under intersection, the
family of *all* its neighbourhoods is a genuine filter — the greatest element of `|E|`. -/
def improperTop (E : NeighborhoodSystem γ)
    (hcl : ∀ {X Y : Set γ}, E.mem X → E.mem Y → E.mem (X ∩ Y)) : E.Element where
  mem := E.mem
  sub h := h
  master_mem := E.master_mem
  inter_mem h1 h2 := hcl h1 h2
  up_mem _ hY _ := hY

end Counterexample712C

end DomainTheory.NeighbourhoodSystems

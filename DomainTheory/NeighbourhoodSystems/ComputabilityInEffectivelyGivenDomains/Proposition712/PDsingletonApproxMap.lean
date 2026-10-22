module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition711
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.PDsingleton_mono

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Proposition 7.12 — the singleton approximable map `λ x. {x}`.** Built from Exercise 2.8's
extension principle: on the finite element `↑X` the value is `{↑X}`. -/
def PDsingletonApproxMap : ApproximableMap V V.PowerDomain :=
  ofMono (fun _X hX => V.PDsingleton (V.principal hX))
    (fun X X' hX hX' hX'X => @PDsingleton_mono α V X X' hX hX' hX'X)

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems

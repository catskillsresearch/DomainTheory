/-ai
The binary finite join of x and y equals the meet of the singleton of x and the singleton of y.

By extensionality, after unfolding meet membership, singleton membership, and the binary finite join, a join witness is a two-component family of neighbourhoods, a power-domain neighbourhood, and component inclusions, and its two components are the two singleton witnesses. Conversely the two singleton witnesses, the first of which supplies the power-domain neighbourhood, assemble into that family, and both the neighbourhood condition and the inclusions hold by cases on the two indices.
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

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)








/-- **Proposition 7.12 — binary intersection law (elementwise).** `{x, y} = {x} ∩ {y}`. -/
theorem PDfinJoin_pair (x y : V.Element) :
    V.PDfinJoin 2 ![x, y] = V.PDsingletonMeet (V.PDsingleton x) (V.PDsingleton y) := by
  apply PDext
  intro W
  simp only [PDsingletonMeet_mem, PDmem_singleton, PDfinJoin, PDmem_finJoinSucc, PDmemFinJoin]
  constructor
  · rintro ⟨X, hX, hPD, hsub⟩
    exact ⟨⟨X 0, hX 0, hPD, hsub 0⟩, ⟨X 1, hX 1, hPD, hsub 1⟩⟩
  · rintro ⟨⟨X0, hx, hPD, hsub0⟩, ⟨X1, hy, _, hsub1⟩⟩
    refine ⟨![X0, X1], ?_, hPD, ?_⟩
    · intro i; fin_cases i <;> assumption
    · intro i; fin_cases i <;> assumption

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems

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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.PDfinJoin_pair

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)








/-- **Proposition 7.12 — binary intersection law (membership form).** `{x, y}` meets `W` iff both
singleton joins do. The general `n`-ary fold `{x₀,…,x_{n-1}} = ⋂ᵢ {xᵢ}` follows by iterating
`PDfinJoin_pair`. -/
theorem PDfinJoin_inter_two (x y : V.Element) {W : Set (Set α)} :
    (V.PDfinJoin 2 ![x, y]).mem W ↔
      (V.PDsingleton x).mem W ∧ (V.PDsingleton y).mem W := by
  rw [← PDsingletonMeet_mem, ← PDfinJoin_pair]

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems

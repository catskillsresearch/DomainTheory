/-ai
The identity map relates two sets if and only if both are neighbourhoods and the first is contained in the second.

This equivalence is the defining relation of the identity map.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic.Set
import all Mathlib.Tactic.Set
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.ApproximableMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.mem_toElementMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.idMap

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

@[simp] theorem idMap_rel {V : NeighborhoodSystem α} {X Y : Set α} :
    (idMap V).rel X Y ↔ V.mem X ∧ V.mem Y ∧ X ⊆ Y := Iff.rfl

end ApproximableMap

end DomainTheory.NeighbourhoodSystems

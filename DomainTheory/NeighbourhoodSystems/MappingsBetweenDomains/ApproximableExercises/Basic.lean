module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import Mathlib.Data.Set.Image
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises.ApproximableMap₂
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises.iSupDirected
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises.ofMono
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises.interMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises.iSupMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises.toElementMap₂

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ : Type*}

namespace NeighborhoodSystem


end NeighborhoodSystem

namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}


end ApproximableMap


namespace ApproximableMap₂

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}


@[simp] theorem mem_toElementMap₂ (f : ApproximableMap₂ V₀ V₁ V₂) (x : V₀.Element) (y : V₁.Element)
    {Z : Set γ} : (f.toElementMap₂ x y).mem Z ↔ ∃ X Y, x.mem X ∧ y.mem Y ∧ f.rel X Y Z := Iff.rfl
end ApproximableMap₂
end DomainTheory.NeighbourhoodSystems

module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise122
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

universe u

variable {α : Type u} {β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

namespace ApproximableMap

/-- **Exercise 2.13 (forward).** The elementwise function of an approximable mapping is continuous.
For an open `U` and `x` with `f(x) ∈ U`, openness gives `Y` with `Y ∈ f(x)` and `[Y] ⊆ U`; unfolding
`Y ∈ f(x)` produces `X ∈ x` with `X f Y`; then `[X] ⊆ f⁻¹U`, since any `x' ∈ [X]` has `Y ∈ f(x')`
(via `X f Y`). -/
theorem continuous_toElementMap (f : ApproximableMap V₀ V₁) :
    Continuous (fun x => f.toElementMap x) := by
  rw [continuous_def]
  intro U hU
  show V₀.OpenFilter _
  constructor
  intro x hx
  obtain ⟨Y, hY, hYU⟩ := hU.out (f.toElementMap x) hx
  obtain ⟨X, hxX, hrel⟩ := hY
  exact ⟨X, hxX, fun x' hx' => hYU ⟨X, hx', hrel⟩⟩

end ApproximableMap
end DomainTheory.NeighbourhoodSystems

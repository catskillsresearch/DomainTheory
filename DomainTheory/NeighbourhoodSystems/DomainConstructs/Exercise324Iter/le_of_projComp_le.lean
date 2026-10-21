/-ai
A map into an iterate lies below another whenever each composite with a coordinate projection lies below the corresponding composite.

On elements, the values are compared by their components. The inequality of the projection composites, rewritten through composition and the projection, is the inequality of those components.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- A map `𝒟₀ → 𝒟₁^∞` is detected coordinate-wise: `f ⊑ f'` iff `projₙ ∘ f ⊑ projₙ ∘ f'` for all `n`. -/
theorem le_of_projComp_le {f f' : ApproximableMap V₀ (iterSys V₁)}
    (h : ∀ n, (projN V₁ n).comp f ≤ (projN V₁ n).comp f') : f ≤ f' := by
  rw [le_iff_toElementMap_le]
  intro x
  apply le_of_component_le
  intro n
  have hx := (le_iff_toElementMap_le.mp (h n)) x
  rwa [toElementMap_comp, toElementMap_comp, toElementMap_projN, toElementMap_projN] at hx

end DomainTheory.NeighbourhoodSystems

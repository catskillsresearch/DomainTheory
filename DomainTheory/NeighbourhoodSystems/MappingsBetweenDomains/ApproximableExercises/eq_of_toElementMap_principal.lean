/-ai
If two approximable maps agree on the principal element of every neighbourhood, then they are equal.

Extensionality of the relation splits on whether the input is a neighbourhood. When it is, each relation is membership in the elementwise image of that principal, and those images agree. When it fails to be a neighbourhood, neither relation holds, because a related input is a neighbourhood.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import Mathlib.Data.Set.Image
import all Mathlib.Data.Set.Image
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ : Type*}


namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}


/-- **Exercise 2.8 (uniqueness).** An approximable mapping is *uniquely determined by its elementwise
effect on finite elements*: if `f(↑X) = g(↑X)` for every neighbourhood `X`, then `f = g`. (Off `𝒟₀`
both relations are empty; on `𝒟₀` use `rel_iff_mem_principal`.) -/
theorem eq_of_toElementMap_principal {f g : ApproximableMap V₀ V₁}
    (h : ∀ (X : Set α) (hX : V₀.mem X),
      f.toElementMap (V₀.principal hX) = g.toElementMap (V₀.principal hX)) : f = g := by
  apply ApproximableMap.ext
  intro X Y
  by_cases hX : V₀.mem X
  · rw [f.rel_iff_mem_principal hX, g.rel_iff_mem_principal hX, h X hX]
  · constructor
    · intro hr; exact absurd (f.rel_dom hr) hX
    · intro hr; exact absurd (g.rel_dom hr) hX

end ApproximableMap
end DomainTheory.NeighbourhoodSystems

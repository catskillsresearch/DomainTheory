/-ai
The strict filter of the strict map represented by an element of the strict function space is that element.

If a neighbourhood belongs to the filter, it is a step neighbourhood of a finite list contained in the upward closure of the represented map, and the step-function characterization puts the element in that neighbourhood. If the element meets a neighbourhood, its subneighbourhood is a step neighbourhood of some list, and the same characterization says the represented map meets every pair of that step.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition68
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510


variable {α β γ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}


/-- `toStrictFilter ∘ toStrictMap = id` (the left inverse of the strict-function-space
representation; the mirror of `toStrictMap_toStrictFilter`). -/
theorem toStrictFilter_toStrictMap (φ : (strictFun V₀ V₁).Element) :
    toStrictFilter (toStrictMap φ) = φ := by
  apply Element.ext
  intro W
  constructor
  · rintro ⟨hWmem, hfW⟩
    obtain ⟨⟨L, hL, rfl⟩, _⟩ := hWmem
    exact (mem_sstepFun_iff φ hL).mpr (fun p hp => hfW p hp)
  · intro hW
    refine ⟨φ.sub hW, ?_⟩
    obtain ⟨⟨L, hL, rfl⟩, _⟩ := φ.sub hW
    intro p hp
    exact (mem_sstepFun_iff φ hL).mp hW p hp

end DomainTheory.NeighbourhoodSystems

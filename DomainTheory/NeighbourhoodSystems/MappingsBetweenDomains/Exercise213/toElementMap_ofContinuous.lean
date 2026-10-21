/-ai
The approximable mapping determined by a continuous function induces that same function on elements.

Elements that contain the same neighbourhoods are equal. The approximable union formula and the continuous union formula both express membership by a neighbourhood of the element whose principal image contains it. On principal elements the monotone extension evaluates to the continuous function, so the witnesses agree in both directions.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise122
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213.Basic
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213.mem_iff_principal_of_continuous

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

universe u

variable {α : Type u} {β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}




namespace ApproximableMap


/-- **Exercise 2.13 — the round trip.** `ofContinuous c hc` induces exactly `c`:
`(ofContinuous c hc)(x) = c(x)` for all `x`. Exercise 2.9 reduces `f(x)` to a union over finite
approximants `↑X` (`X ∈ x`), where `ofMono` evaluates to `c(↑X)`; the union formula
`mem_iff_principal_of_continuous` then re-assembles `c(x)`. -/
theorem toElementMap_ofContinuous (c : V₀.Element → V₁.Element) (hc : Continuous c)
    (x : V₀.Element) : (ofContinuous c hc).toElementMap x = c x := by
  apply Element.ext
  intro Y
  rw [toElementMap_mem_iff_principal, NeighborhoodSystem.mem_iff_principal_of_continuous hc]
  constructor
  · rintro ⟨X, hxX, hmem⟩
    refine ⟨X, hxX, ?_⟩
    rwa [ofContinuous, toElementMap_ofMono_principal] at hmem
  · rintro ⟨X, hxX, hmem⟩
    refine ⟨X, hxX, ?_⟩
    rwa [ofContinuous, toElementMap_ofMono_principal]

end ApproximableMap
end DomainTheory.NeighbourhoodSystems

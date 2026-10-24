module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic.Set
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.ApproximableMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.sSupDirected
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.toElementMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.idMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.comp
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.ofIso
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.ext
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.mem_toElementMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.idMap_rel
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.comp_rel
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.toElementMap_idMap

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}


namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}


/-- **Theorem 2.5 — associativity.** `h ∘ (g ∘ f) = (h ∘ g) ∘ f`. Pure reassociation of the
existential witnesses. -/
theorem comp_assoc {V₃ : NeighborhoodSystem δ} (h : ApproximableMap V₂ V₃)
    (g : ApproximableMap V₁ V₂) (f : ApproximableMap V₀ V₁) :
    (h.comp g).comp f = h.comp (g.comp f) := by
  apply ApproximableMap.ext
  intro X W
  constructor
  · rintro ⟨Y, hXY, Z, hYZ, hZW⟩
    exact ⟨Z, ⟨Y, hXY, hYZ⟩, hZW⟩
  · rintro ⟨Z, ⟨Y, hXY, hYZ⟩, hZW⟩
    exact ⟨Y, hXY, Z, hYZ, hZW⟩

end ApproximableMap
end DomainTheory.NeighbourhoodSystems

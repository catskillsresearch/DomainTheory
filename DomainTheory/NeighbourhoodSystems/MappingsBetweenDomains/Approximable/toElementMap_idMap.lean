/-ai
The elementwise action of the identity map is the identity function on elements.

Extensionality of elements splits the equality. A neighbourhood of the image is contained in a neighbourhood of the element, so upward closure puts it in the element. A neighbourhood of the element is related to itself by the identity.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic.Set
import all Mathlib.Tactic.Set
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.ApproximableMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.ext
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.toElementMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.mem_toElementMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.idMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.idMap_rel
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.comp_rel

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

@[simp] theorem toElementMap_idMap (x : V₀.Element) : (idMap V₀).toElementMap x = x := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X, hXx, _, hY, hXY⟩
    exact x.up_mem hXx hY hXY
  · intro hY
    exact ⟨Y, hY, x.sub hY, x.sub hY, subset_rfl⟩

end ApproximableMap

end DomainTheory.NeighbourhoodSystems

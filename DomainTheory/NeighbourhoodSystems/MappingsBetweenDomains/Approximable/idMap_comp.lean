/-ai
Composing the identity map on the left with an approximable map returns the original map.

Extensionality of the relation splits the equality. A composite witness is an inclusion of the intermediate neighbourhood in the output, and monotonicity enlarges the output of the map along that inclusion. In the other direction the output neighbourhood itself is an identity witness.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic.Set
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}


namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}


/-- **Theorem 2.5 — left identity law.** `I_{D₁} ∘ f = f`. (`→`: a witness `Y ⊆ Z` widens the output
of `f` by `f.mono`; `←`: take `Y = Z`.) -/
theorem idMap_comp (f : ApproximableMap V₀ V₁) : (idMap V₁).comp f = f := by
  apply ApproximableMap.ext
  intro X Z
  constructor
  · rintro ⟨Y, hXY, _, hZ, hYZ⟩
    exact f.mono hXY subset_rfl hYZ (f.rel_dom hXY) hZ
  · intro hXZ
    exact ⟨Z, hXZ, f.rel_cod hXZ, f.rel_cod hXZ, subset_rfl⟩

end ApproximableMap
end DomainTheory.NeighbourhoodSystems

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


/-- **Theorem 2.5 — right identity law.** `f ∘ I_{D₀} = f`. (`→`: a witness `X ⊆ Y` sharpens the
input of `f` by `f.mono`; `←`: take `Y = X`.) -/
theorem comp_idMap (f : ApproximableMap V₀ V₁) : f.comp (idMap V₀) = f := by
  apply ApproximableMap.ext
  intro X Z
  constructor
  · rintro ⟨Y, ⟨hX, _, hXY⟩, hYZ⟩
    exact f.mono hYZ hXY subset_rfl hX (f.rel_cod hYZ)
  · intro hXZ
    exact ⟨X, ⟨f.rel_dom hXZ, f.rel_dom hXZ, subset_rfl⟩, hXZ⟩

end ApproximableMap
end DomainTheory.NeighbourhoodSystems

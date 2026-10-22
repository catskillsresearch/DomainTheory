/-ai
For a neighbourhood X, an approximable map relates X to Y if and only if Y belongs to the elementwise image of the principal element on X.

In one direction X belongs to its own principal element. In the other direction a witnessing neighbourhood of that principal contains X, and monotonicity of the relation replaces the input by X.
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


/-- **Proposition 2.2(ii) (Scott 1981, PRG-19).** The relation is recovered from the elementwise
map: for `X ∈ 𝒟₀`, `X f Y ↔ Y ∈ f(↑X)`. (`→` since `X ∈ ↑X`; `←` since any `Z ∈ ↑X` has `X ⊆ Z`,
so `Z f Y` monotonically yields `X f Y`.) -/
theorem rel_iff_mem_principal (f : ApproximableMap V₀ V₁) {X : Set α} (hX : V₀.mem X) {Y : Set β} :
    f.rel X Y ↔ (f.toElementMap (V₀.principal hX)).mem Y := by
  constructor
  · intro hXY
    exact ⟨X, ⟨hX, subset_rfl⟩, hXY⟩
  · rintro ⟨Z, ⟨_, hXZ⟩, hZY⟩
    exact f.mono hZY hXZ subset_rfl hX (f.rel_cod hZY)

end ApproximableMap
end DomainTheory.NeighbourhoodSystems

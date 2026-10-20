module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example62 ExampleB

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}











variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}















































/-- **Exercise 6.19 — *"Are these correct up to isomorphism?"* (product).** Scott's uniform
`{0,1}*`-presentation `𝒟₀ × 𝒟₁` is isomorphic, as a domain, to the abstract product of Definition 3.1.
Both compute the same domain `|D₀| × |D₁|` (via `prodTokEquiv` and Scott's `prodEquiv`). -/
theorem prodTok_iso_prod : prodTok D₀ D₁ ≅ᴰ prod D₀ D₁ :=
  ⟨prodTokEquiv.trans (prodEquiv D₀ D₁).symm⟩

end Exercise619
end DomainTheory.NeighbourhoodSystems

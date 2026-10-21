/-ai
The concrete token sum of Exercise 6.19 is isomorphic, as a domain, to the abstract separated sum.

The isomorphism is the order isomorphism between their elements.
ai-/
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






















/-- **Exercise 6.19 — *"Are these correct up to isomorphism?"* (sum).** Scott's uniform
`{0,1}*`-presentation `𝒟₀ + 𝒟₁` is isomorphic, as a domain, to the abstract separated sum of
Exercise 3.18. -/
theorem sumTok_iso_sum : sumTok D₀ D₁ h₀ h₁ ≅ᴰ sum D₀ D₁ h₀ h₁ := ⟨sumTokEquiv⟩

end Exercise619
end DomainTheory.NeighbourhoodSystems

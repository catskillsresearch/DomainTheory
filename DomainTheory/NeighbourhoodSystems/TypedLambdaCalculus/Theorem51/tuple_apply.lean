/-ai
Theorem 5.1, tuple case (Scott 1981, PRG-19), states that the pairing of two approximable maps sends an element to the pair of their values at that element.

This is the pairing law on elements.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem51.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

namespace Theorem51




/-- **Theorem 5.1, tuple case (Scott 1981, PRG-19).** If `⟦σ₀⟧, ⟦σ₁⟧` are approximable, so is the
tuple `⟨⟦σ₀⟧, ⟦σ₁⟧⟩ = paired`, with value `⟨σ₀(w), σ₁(w)⟩`. -/
theorem tuple_apply (f : ApproximableMap V₂ V₀) (g : ApproximableMap V₂ V₁) (w : V₂.Element) :
    (paired f g).toElementMap w = pair (f.toElementMap w) (g.toElementMap w) :=
  toElementMap_paired f g w

end Theorem51
end DomainTheory.NeighbourhoodSystems

/-ai
Postcomposing the diagonal with the first projection returns the identity map.

The identity is the corresponding fact for the pairing of the identity with itself.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise314.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} (V : NeighborhoodSystem α)


/-- **Exercise 3.14 (Scott 1981, PRG-19).** Post-composing the diagonal with the two projections
returns the identity: `p₀ ∘ diag = I` and `p₁ ∘ diag = I`. -/
theorem proj₀_comp_diag : (proj₀ V V).comp (diag V) = idMap V :=
  proj₀_comp_paired (idMap V) (idMap V)

end DomainTheory.NeighbourhoodSystems

/-ai
Theorem 5.1, constant case (Scott 1981, PRG-19), states that the constant map with value k sends every element to k.

This is the value law of the constant map.
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


/-- **Theorem 5.1, constant case (Scott 1981, PRG-19).** A constant `k` is interpreted by the
constant map, which is approximable with value `k`. -/
theorem const_apply (k : V₁.Element) (x : V₀.Element) :
    (constMap V₀ k).toElementMap x = k := toElementMap_constMap k x

end Theorem51
end DomainTheory.NeighbourhoodSystems

/-ai
The embedding sends a paired element to the pair of the truth element with the pair of the left injection of the first value and the right injection of the second value.

Unfold the embedding and simplify by the element maps of pairing, composition, and the two projections, together with the two components of a pair.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}




theorem condSumEmb_toElementMap (t : TD.Element) (x : V₀.Element) (y : V₁.Element) :
    (condSumEmb V₀ V₁ h₀ h₁).toElementMap (pair t (pair x y))
      = pair t (pair ((inMap₀ (h₀ := h₀) (h₁ := h₁)).toElementMap x)
          ((inMap₁ (h₀ := h₀) (h₁ := h₁)).toElementMap y)) := by
  simp only [condSumEmb, toElementMap_paired, toElementMap_comp, toElementMap_proj₀,
    toElementMap_proj₁, fst_pair, snd_pair]

end DomainTheory.NeighbourhoodSystems.Exercise326

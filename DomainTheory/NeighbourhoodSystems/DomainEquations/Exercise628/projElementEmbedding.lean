module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

/-- **The element-wise map of an injection `i` is an order embedding.** Given approximable maps
`i : D → E`, `j : E → D` with `j ∘ i = I_D`, the map `x ↦ i(x)` on elements is an order embedding
`|D| ↪o |E|`: monotone by `toElementMap_mono`, and order-reflecting because `j(·)` is a monotone
left inverse (`j(i(x)) = x`). Choice-free. -/
def projElementEmbedding {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}
    (i : ApproximableMap D E) (j : ApproximableMap E D) (hji : j.comp i = idMap D) :
    D.Element ↪o E.Element :=
  OrderEmbedding.ofMapLEIff i.toElementMap (by
    have hround : ∀ x : D.Element, j.toElementMap (i.toElementMap x) = x := by
      intro x; rw [← toElementMap_comp, hji, toElementMap_idMap]
    intro a b
    constructor
    · intro h
      have hjm := toElementMap_mono j h
      rwa [hround a, hround b] at hjm
    · intro h
      exact toElementMap_mono i h)

end DomainTheory.NeighbourhoodSystems

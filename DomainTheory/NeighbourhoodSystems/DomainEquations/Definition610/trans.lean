/-ai
The subsystem relation is transitive.

The masters agree by composing the two master equalities. A neighbourhood of the first system is a neighbourhood of the second and therefore of the third. If the intersection of two neighbourhoods of the first system is a neighbourhood of the third, those two neighbourhoods belong to the second system, the second subsystem relation places the intersection in the second system, and the first subsystem relation then places it in the first system.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

variable {α : Type*}


namespace Subsystem

/-- The subsystem relation is **transitive**: `D ◁ E` and `E ◁ F` give `D ◁ F`.

The `inter_closed` clause threads through `E`: from `X, Y ∈ D ⊆ E` and `X ∩ Y ∈ F`, the relation
`E ◁ F` puts `X ∩ Y ∈ E`, and then `D ◁ E` puts `X ∩ Y ∈ D`. -/
theorem trans {D E F : NeighborhoodSystem α} (h₁ : D ◁ E) (h₂ : E ◁ F) : D ◁ F where
  master_eq := h₁.master_eq.trans h₂.master_eq
  sub h := h₂.sub (h₁.sub h)
  inter_closed hX hY hXY :=
    h₁.inter_closed hX hY (h₂.inter_closed (h₁.sub hX) (h₁.sub hY) hXY)

end Subsystem
end DomainTheory.NeighbourhoodSystems

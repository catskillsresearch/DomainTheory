/-ai
When the base element is the least fixed point of f, every fixed point of the restricted map is the restriction of that least fixed point to itself.

The embedding of such a fixed point is fixed by f, because the action of the restriction under the embedding and the fixed-point equation identify its image with itself, and the embedding lies below the least fixed point, so uniqueness below the least fixed point makes the embedding equal that least fixed point. Restricting the embedding recovers the original filter. The restriction of the embedding and the restriction of the least fixed point agree by extensionality once those underlying elements agree. Composing these equalities gives the claim.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.relMap_toElementMap_embed
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.fixElement_below_unique

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap
















/-- **Exercise 4.10 (Scott 1981, PRG-19).** With `a = fix(f)`, the restricted map `f'` has *exactly
one* fixed point: the top element of `D_{fix f}`, namely `restrict (fix f)` of `fix f` itself. Every
`Dₐ`-fixed point `g` of `f'` satisfies `embed a g = fix f`, hence is this top element. -/
theorem relMap_unique_fixed (f : ApproximableMap V V)
    (ha : f.toElementMap f.fixElement = f.fixElement) (g : (relSystem f.fixElement).Element)
    (hg : (relMap f ha).toElementMap g = g) :
    g = restrict f.fixElement f.fixElement (le_refl _) := by
  -- `embed g` is a fixed point of `f` below `fix f`, hence equals `fix f`.
  have hembfix : f.toElementMap (embed f.fixElement g) = embed f.fixElement g := by
    rw [← relMap_toElementMap_embed f ha g, hg]
  have heq : embed f.fixElement g = f.fixElement :=
    fixElement_below_unique f (embed_le f.fixElement g) hembfix
  -- transport along the iso.
  have h1 : restrict f.fixElement (embed f.fixElement g) (embed_le f.fixElement g) = g :=
    restrict_embed f.fixElement g
  -- both restricts agree because their underlying elements agree.
  have h2 : restrict f.fixElement (embed f.fixElement g) (embed_le f.fixElement g)
      = restrict f.fixElement f.fixElement (le_refl _) := by
    apply Element.ext
    intro X
    show (embed f.fixElement g).mem X ↔ f.fixElement.mem X
    rw [heq]
  rw [← h1, h2]

end ApproximableMap
end DomainTheory.NeighbourhoodSystems

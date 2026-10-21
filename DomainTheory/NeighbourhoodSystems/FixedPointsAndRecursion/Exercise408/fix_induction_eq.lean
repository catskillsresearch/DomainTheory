/-ai
If two approximable endomaps a and b agree at bottom, and an approximable endomap f commutes with each of them, then a and b agree at the least fixed point of f.

Commutation of the maps, rewritten by the composition law for elementwise actions, gives a(f(x)) equal to f(a(x)) and b(f(x)) equal to f(b(x)). Fixed-point induction is applied to agreement of a and b. The base case is the given agreement at bottom. The inductive step rewrites both sides by those commutation identities and uses the inductive agreement. For a monotone chain, both images of the supremum are directed unions of the images of the terms; extensionality reduces the comparison to membership in those unions, and pointwise agreement of the images transfers the witnesses in both directions.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise408.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise408.fix_induction

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap


/-- **Exercise 4.8 (Scott 1981, PRG-19) — application to `S = {x ∣ a(x) = b(x)}`.** If `a(⊥) = b(⊥)`
and `f` commutes with both `a` and `b` (`f ∘ a = a ∘ f`, `f ∘ b = b ∘ f`), then `a` and `b` agree at
the least fixed point: `a(fix f) = b(fix f)`. -/
theorem fix_induction_eq (f a b : ApproximableMap V V)
    (hbot : a.toElementMap V.bot = b.toElementMap V.bot)
    (hfa : f.comp a = a.comp f) (hfb : f.comp b = b.comp f) :
    a.toElementMap f.fixElement = b.toElementMap f.fixElement := by
  -- commutation, elementwise: `a(f x) = f(a x)` and `b(f x) = f(b x)`.
  have hca : ∀ x, a.toElementMap (f.toElementMap x) = f.toElementMap (a.toElementMap x) := by
    intro x
    have h1 : (a.comp f).toElementMap x = (f.comp a).toElementMap x := by rw [hfa]
    rwa [toElementMap_comp, toElementMap_comp] at h1
  have hcb : ∀ x, b.toElementMap (f.toElementMap x) = f.toElementMap (b.toElementMap x) := by
    intro x
    have h1 : (b.comp f).toElementMap x = (f.comp b).toElementMap x := by rw [hfb]
    rwa [toElementMap_comp, toElementMap_comp] at h1
  refine fix_induction f (fun x => a.toElementMap x = b.toElementMap x) hbot ?_ ?_
  · intro x hx
    rw [hca, hcb, hx]
  · intro s hmono hs
    -- both sides are directed unions of equal families.
    show a.toElementMap (supChain s hmono) = b.toElementMap (supChain s hmono)
    rw [supChain, toElementMap_iSupDirected, toElementMap_iSupDirected]
    apply Element.ext
    intro Z
    rw [NeighborhoodSystem.mem_iSupDirected, NeighborhoodSystem.mem_iSupDirected]
    constructor
    · rintro ⟨n, hn⟩; exact ⟨n, by rw [← hs n]; exact hn⟩
    · rintro ⟨n, hn⟩; exact ⟨n, by rw [hs n]; exact hn⟩

end ApproximableMap
end DomainTheory.NeighbourhoodSystems

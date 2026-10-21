/-ai
If the second injection is injective, Tarski's map is surjective.

For an element of the codomain, split on whether its image under the second injection lies in the fixed set. If it does, rewrite by the fixed-point equation: the complement-of-range alternative contradicts that this image lies in the range, and the image alternative supplies an element of the fixed set whose image under both maps has the same image under the second injection, so injectivity recovers the codomain element and the map agrees with the first injection there. If it does not, the map at that image is a preimage, and injectivity of the second injection applied to the preimage equation recovers the codomain element.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise424.sbSet
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise424.sbSet_isFixed
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise424.sbFun
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise424.sbFun_mem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise424.g_sbFun_not_mem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise424

open DomainTheory.NeighbourhoodSystems.Exercise414 Function

variable {A B : Type*} {f : A → B} {g : B → A}

theorem sbFun_surjective (hg : Injective g) : Surjective (sbFun f g) := by
  intro b
  by_cases hb : g b ∈ sbSet f g
  · -- `g b ∈ X = T X`; not in `(range g)ᶜ`, so `g b ∈ g(f(X))`.
    rw [← sbSet_isFixed] at hb
    rcases hb with hb | ⟨y, ⟨a, ha, rfl⟩, hgy⟩
    · exact absurd ⟨b, rfl⟩ hb
    · refine ⟨a, ?_⟩
      rw [sbFun_mem ha, hg hgy]
  · -- `g b ∉ X`: then `h (g b) = b`.
    refine ⟨g b, ?_⟩
    exact hg (g_sbFun_not_mem hb)

end DomainTheory.NeighbourhoodSystems.Exercise424

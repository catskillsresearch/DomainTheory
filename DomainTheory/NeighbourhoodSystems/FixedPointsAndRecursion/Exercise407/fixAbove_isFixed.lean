/-ai
The directed union x of the iterates of an approximable endomap f, starting from a pre-fixed point a, is a fixed point of f.

For f(x) below x, the image of the directed union is the directed union of the images, the image of the n-th iterate is the next iterate, and each successor iterate lies below the union. For x below f(x), each iterate lies below the next by monotonicity of the iteration, the next iterate is the image of the previous one, and that image lies below f(x) because the previous iterate lies below the union and f is monotone.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise407.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap







/-- **Exercise 4.7 (Scott 1981, PRG-19).** `fixAbove f ha` is a fixed point: `f(x) = x`. -/
theorem fixAbove_isFixed (f : ApproximableMap V V) {a : V.Element} (ha : a ≤ f.toElementMap a) :
    f.toElementMap (f.fixAbove ha) = f.fixAbove ha := by
  set hdir := (fun i j => ⟨max i j, iterFrom_mono f ha (le_max_left i j),
    iterFrom_mono f ha (le_max_right i j)⟩ :
    ∀ i j, ∃ k, f.iterFrom a i ≤ f.iterFrom a k ∧ f.iterFrom a j ≤ f.iterFrom a k) with hdir_def
  apply le_antisymm
  · -- `f(x) = ⊔ₙ f(fⁿ(a)) = ⊔ₙ f^{n+1}(a) ⊑ x` since each `f^{n+1}(a) ⊑ x`.
    rw [fixAbove, toElementMap_iSupDirected]
    apply NeighborhoodSystem.iSupDirected_le
    intro n
    have : f.toElementMap (f.iterFrom a n) = f.iterFrom a (n + 1) := (iterFrom_succ f a n).symm
    rw [this]
    exact NeighborhoodSystem.le_iSupDirected (f.iterFrom a) hdir (n + 1)
  · -- `x ⊑ f(x)`: each `fⁿ(a) ⊑ fⁿ⁺¹(a) = f(fⁿ(a)) ⊑ f(x)`.
    apply NeighborhoodSystem.iSupDirected_le
    intro n
    calc f.iterFrom a n
        ≤ f.iterFrom a (n + 1) := iterFrom_mono f ha (Nat.le_succ n)
      _ = f.toElementMap (f.iterFrom a n) := iterFrom_succ f a n
      _ ≤ f.toElementMap (f.fixAbove ha) :=
          f.toElementMap_mono (NeighborhoodSystem.le_iSupDirected (f.iterFrom a) hdir n)

end ApproximableMap
end DomainTheory.NeighbourhoodSystems

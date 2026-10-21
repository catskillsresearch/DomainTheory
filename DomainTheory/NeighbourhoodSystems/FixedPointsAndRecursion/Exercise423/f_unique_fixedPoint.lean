/-ai
If an approximable endomap admits a sequence of approximable maps that is constantly bottom at stage zero, has each element as the least upper bound of the values of the sequence there, and satisfies the commutation that the next approximant after the map equals the next approximant after the map after the current approximant, then the endomap has a unique fixed point.

The least fixed point is fixed by the fixed-point law, and it lies below any fixed point by minimality. By induction on the stage, the approximant of a fixed point lies below the approximant of the least fixed point: at zero the approximant is bottom, and at a successor the fixed-point equations and the commutation rewrite both sides so that monotonicity of the next approximant and of the endomap apply to the inductive inequality. Each approximant of the least fixed point lies below it because it is an upper bound of its own scheme, so the least fixed point is an upper bound of the approximants of the given fixed point and the least-upper-bound property places that fixed point below the least one. The two inequalities give equality.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise423.Basic

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.toElementMap_fixElement
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- **Exercise 4.23 (Scott 1981, PRG-19) — Eilenberg.** If `f` is approximable and `aₙ` is an
*approximation scheme* — (i) `a₀ = ⊥`, (ii) increasing, (iii) `⊔ₙ aₙ = I` (pointwise `IsLUB`),
(iv) `aₙ₊₁ ∘ f = aₙ₊₁ ∘ f ∘ aₙ` — then `f` has a **unique** fixed point.

The unique fixed point is `fix f` (Theorem 4.1). -/
theorem f_unique_fixedPoint (f : ApproximableMap V V) (a : ℕ → ApproximableMap V V)
    (ha0 : ∀ x, (a 0).toElementMap x = V.bot)
    (hlub : ∀ x, IsLUB {y | ∃ n, y = (a n).toElementMap x} x)
    (hcomm : ∀ n x, (a (n + 1)).toElementMap (f.toElementMap x) =
      (a (n + 1)).toElementMap (f.toElementMap ((a n).toElementMap x))) :
    ∃! x, f.toElementMap x = x := by
  set fix := f.fixElement with hfixdef
  have hfixed : f.toElementMap fix = fix := toElementMap_fixElement f
  refine ⟨fix, hfixed, ?_⟩
  intro x hx
  -- `fix ⊑ x`: minimality of the least fixed point.
  have hle : fix ≤ x := fixElement_le_of_toElementMap_le f (le_of_eq hx)
  -- `aₙ(x) ⊑ aₙ(fix)` by induction on `n` (Scott's hint).
  have approx_le : ∀ n, (a n).toElementMap x ≤ (a n).toElementMap fix := by
    intro n
    induction n with
    | zero => rw [ha0 x]; exact bot_le
    | succ k ih =>
      have h1 : (a (k + 1)).toElementMap x =
          (a (k + 1)).toElementMap (f.toElementMap ((a k).toElementMap x)) := by
        rw [← hcomm k x, hx]
      have h2 : (a (k + 1)).toElementMap (f.toElementMap ((a k).toElementMap fix)) =
          (a (k + 1)).toElementMap fix := by
        rw [← hcomm k fix, hfixed]
      rw [h1, ← h2]
      exact toElementMap_mono (a (k + 1)) (toElementMap_mono f ih)
  -- each `aₙ(fix) ⊑ fix` (since `fix` is an upper bound of its own scheme).
  have hfix_ub : ∀ n, (a n).toElementMap fix ≤ fix := fun n => (hlub fix).1 ⟨n, rfl⟩
  -- so `fix` is an upper bound of `{aₙ(x)}`, hence `x = ⊔ₙ aₙ(x) ⊑ fix`.
  have hge : x ≤ fix := by
    apply (hlub x).2
    rintro y ⟨n, rfl⟩
    exact le_trans (approx_le n) (hfix_ub n)
  exact le_antisymm hge hle

end ApproximableMap
end DomainTheory.NeighbourhoodSystems

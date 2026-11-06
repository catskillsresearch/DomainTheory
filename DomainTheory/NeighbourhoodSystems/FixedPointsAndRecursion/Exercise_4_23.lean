module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.bot_le
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableMap

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem_4_2
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.bot
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Basic.ExistsUnique

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap
section
variable {α : Type*} {V : NeighborhoodSystem α}
namespace ApproximableMap

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

  have hle : fix ≤ x := fixElement_le_of_toElementMap_le f (le_of_eq hx)

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

  have hfix_ub : ∀ n, (a n).toElementMap fix ≤ fix := fun n => (hlub fix).1 ⟨n, rfl⟩

  have hge : x ≤ fix := by
    apply (hlub x).2
    rintro y ⟨n, rfl⟩
    exact le_trans (approx_le n) (hfix_ub n)
  exact le_antisymm hge hle

end ApproximableMap
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.ApproximableMap
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

theorem example_423 :
    ∀ {α : Type*} {V : NeighborhoodSystem α}
      (f : ApproximableMap V V) (a : ℕ → ApproximableMap V V),
      (∀ x, (a 0).toElementMap x = V.bot) →
      (∀ x, IsLUB {y | ∃ n, y = (a n).toElementMap x} x) →
      (∀ n x, (a (n + 1)).toElementMap (f.toElementMap x) =
        (a (n + 1)).toElementMap (f.toElementMap ((a n).toElementMap x))) →
      ∃! x, f.toElementMap x = x :=
  @f_unique_fixedPoint

end DomainTheory.NeighbourhoodSystems.ApproximableMap
end

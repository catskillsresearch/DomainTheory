module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise_3_25
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_23
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_24
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_8
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Submonoid.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Definition_2_1
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Theorem_2_5
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_2
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example_2_3
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_11
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_8
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_9

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
/- concordance: source L2351 EXERCISE 4.23 commuting with the iterates -/
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
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.ApproximableMap
section
set_option linter.unusedVariables false

theorem example_423.{u_1} : ∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
  (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
  (a : Nat → @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V),
  (∀ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V
          (a (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) x)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot α V)) →
    (∀ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
        @IsLUB (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
          (@Set.ofPred (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            fun (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) =>
            ∃ (n : Nat),
              @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) y
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V (a n) x))
          x) →
      (∀ (n : Nat) (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V
              (a
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f x))
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V
              (a
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V (a n) x)))) →
        @ExistsUnique (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          fun (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) =>
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f x) x :=
  @DomainTheory.NeighbourhoodSystems.ApproximableMap.f_unique_fixedPoint
end

end DomainTheory.NeighbourhoodSystems.ApproximableMap
end

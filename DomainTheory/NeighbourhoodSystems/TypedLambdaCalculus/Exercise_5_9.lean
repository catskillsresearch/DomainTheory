module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise_4_11
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise_4_7
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem_4_2
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise_5_8

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap
section
variable {α : Type*} {V : NeighborhoodSystem α}
namespace ApproximableMap
/- concordance: source L3015 EXERCISE 5.9 common fixed points -/
/-- **Exercise 5.9 (Scott 1981, PRG-19).** Commuting approximable maps have a *least common fixed
point* `x = f(x) = g(x)`. -/
theorem commuting_least_common_fixed {f g : ApproximableMap V V} (hcomm : f.comp g = g.comp f) :
    ∃ x : V.Element, f.toElementMap x = x ∧ g.toElementMap x = x ∧
      ∀ w : V.Element, f.toElementMap w = w → g.toElementMap w = w → x ≤ w := by
  set a := f.fixElement with ha_def
  have hfa : f.toElementMap a = a := toElementMap_fixElement f
  -- `a ⊑ g(a)` since `g(a)` is a fixed point of `f`.
  have ha_le : a ≤ g.toElementMap a := by
    apply fixElement_le_of_toElementMap_le f
    rw [commute_apply hcomm, hfa]
  set x := g.fixAbove ha_le with hx_def
  have hgx : g.toElementMap x = x := fixAbove_isFixed g ha_le
  have hax : a ≤ x := le_fixAbove g ha_le
  -- each `gⁿ(a)` is a fixed point of `f`.
  have hfix_each : ∀ n, f.toElementMap (g.iterFrom a n) = g.iterFrom a n := by
    intro n
    induction n with
    | zero => rw [iterFrom_zero]; exact hfa
    | succ k ih =>
      rw [iterFrom_succ g a k, commute_apply hcomm, ih]
  -- so `f(x) = x` by continuity.
  have hfx : f.toElementMap x = x := by
    apply le_antisymm
    · rw [hx_def, fixAbove, toElementMap_iSupDirected]
      apply NeighborhoodSystem.iSupDirected_le
      intro n
      rw [hfix_each n]
      exact NeighborhoodSystem.le_iSupDirected (g.iterFrom a) _ n
    · rw [hx_def, fixAbove]
      apply NeighborhoodSystem.iSupDirected_le
      intro n
      rw [← hfix_each n]
      exact f.toElementMap_mono (NeighborhoodSystem.le_iSupDirected (g.iterFrom a) _ n)
  refine ⟨x, hfx, hgx, ?_⟩
  intro w hfw hgw
  have haw : a ≤ w := fixElement_le_of_toElementMap_le f (le_of_eq hfw)
  exact fixAbove_least g ha_le haw (le_of_eq hgw)

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

theorem iterElem_zero' (f : ApproximableMap V V) : f.iterElem 0 = V.bot := by
  rw [iterElem_eq_iterate, Function.iterate_zero_apply]

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- `(f²)ⁿ(⊥) = f^{2n}(⊥)`. -/
theorem comp_self_iterElem (f : ApproximableMap V V) (n : ℕ) :
    (f.comp f).iterElem n = f.iterElem (2 * n) := by
  induction n with
  | zero => rw [iterElem_zero', Nat.mul_zero, iterElem_zero']
  | succ k ih =>
    have h2 : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
    rw [iterElem_succ, ih, toElementMap_comp, h2, iterElem_succ, iterElem_succ]

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- **Exercise 5.9 (Scott 1981, PRG-19).** If `f, g` commute and `f(⊥) = g(⊥)`, then
`fix(f) = fix(g)`. -/
theorem fixElement_eq_of_commuting_bot {f g : ApproximableMap V V} (hcomm : f.comp g = g.comp f)
    (hbot : f.toElementMap V.bot = g.toElementMap V.bot) :
    f.fixElement = g.fixElement := by
  -- `g(fⁿ⊥) = fⁿ⁺¹⊥`.
  have hshift : ∀ n, g.toElementMap (f.iterElem n) = f.iterElem (n + 1) := by
    intro n
    induction n with
    | zero =>
      rw [iterElem_zero', iterElem_succ, iterElem_zero', ← hbot]
    | succ k ih =>
      rw [iterElem_succ, ← commute_apply hcomm, ih]
      exact (iterElem_succ f (k + 1)).symm
  -- `g(fix f) = fix f`.
  have hgfixf : g.toElementMap f.fixElement = f.fixElement := by
    rw [fixElement_eq_iSupDirected f, toElementMap_iSupDirected]
    apply le_antisymm
    · apply NeighborhoodSystem.iSupDirected_le
      intro n
      rw [hshift n]
      exact NeighborhoodSystem.le_iSupDirected f.iterElem _ (n + 1)
    · apply NeighborhoodSystem.iSupDirected_le
      intro n
      calc f.iterElem n ≤ f.iterElem (n + 1) := iterElem_mono f (Nat.le_succ n)
        _ = g.toElementMap (f.iterElem n) := (hshift n).symm
        _ ≤ _ := NeighborhoodSystem.le_iSupDirected (fun m => g.toElementMap (f.iterElem m)) _ n
  -- symmetric: `f(fix g) = fix g`.
  have hshift' : ∀ n, f.toElementMap (g.iterElem n) = g.iterElem (n + 1) := by
    intro n
    induction n with
    | zero =>
      rw [iterElem_zero', iterElem_succ, iterElem_zero', hbot]
    | succ k ih =>
      rw [iterElem_succ, commute_apply hcomm, ih]
      exact (iterElem_succ g (k + 1)).symm
  have hffixg : f.toElementMap g.fixElement = g.fixElement := by
    rw [fixElement_eq_iSupDirected g, toElementMap_iSupDirected]
    apply le_antisymm
    · apply NeighborhoodSystem.iSupDirected_le
      intro n
      rw [hshift' n]
      exact NeighborhoodSystem.le_iSupDirected g.iterElem _ (n + 1)
    · apply NeighborhoodSystem.iSupDirected_le
      intro n
      calc g.iterElem n ≤ g.iterElem (n + 1) := iterElem_mono g (Nat.le_succ n)
        _ = f.toElementMap (g.iterElem n) := (hshift' n).symm
        _ ≤ _ := NeighborhoodSystem.le_iSupDirected (fun m => f.toElementMap (g.iterElem m)) _ n
  apply le_antisymm
  · exact fixElement_le_of_toElementMap_le f (le_of_eq hffixg)
  · exact fixElement_le_of_toElementMap_le g (le_of_eq hgfixf)

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- **Exercise 5.9 (Scott 1981, PRG-19).** In particular `fix(f) = fix(f²)`: the `f²`-chain
`f^{2n}(⊥)` is cofinal in the `f`-chain `fⁿ(⊥)`, so the two least fixed points coincide. -/
theorem fixElement_iterTwice (f : ApproximableMap V V) :
    f.fixElement = (f.comp f).fixElement := by
  apply le_antisymm
  · -- `fix f ⊑ fix f²`: `fⁿ⊥ ⊑ f^{2n}⊥ = (f²)ⁿ⊥ ⊑ fix f²`.
    rw [fixElement_eq_iSupDirected f]
    apply NeighborhoodSystem.iSupDirected_le
    intro n
    calc f.iterElem n ≤ f.iterElem (2 * n) := iterElem_mono f (by omega)
      _ = (f.comp f).iterElem n := (comp_self_iterElem f n).symm
      _ ≤ (f.comp f).fixElement := iterElem_le_fixElement (f.comp f) n
  · -- `fix f² ⊑ fix f`: `fix f` is a fixed point of `f²`.
    refine fixElement_le_of_toElementMap_le (f.comp f) (le_of_eq ?_)
    rw [toElementMap_comp, toElementMap_fixElement, toElementMap_fixElement]

end ApproximableMap
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.ApproximableMap
section
set_option linter.unusedVariables false

theorem example_509.{u_1} : And
  (And
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {f g : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V},
      @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V f g)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V g f) →
        ∃ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
          And
            (@Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f x) x)
            (And
              (@Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V g x) x)
              (∀ (w : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
                @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f w) w →
                  @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V g w) w →
                    @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
                      x w)))
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {f g : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V},
      @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V f g)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V g f) →
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot α V))
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V g
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot α V)) →
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V g)))
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V f f))) :=
  @And.intro
  (And
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {f g : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V},
      @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V f g)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V g f) →
        ∃ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
          And
            (@Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f x) x)
            (And
              (@Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V g x) x)
              (∀ (w : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
                @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f w) w →
                  @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V g w) w →
                    @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
                      x w)))
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {f g : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V},
      @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V f g)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V g f) →
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot α V))
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V g
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot α V)) →
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V g)))
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V f f)))
  (@And.intro
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {f g : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V},
      @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V f g)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V g f) →
        ∃ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
          And
            (@Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f x) x)
            (And
              (@Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V g x) x)
              (∀ (w : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
                @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f w) w →
                  @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V g w) w →
                    @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
                      x w)))
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {f g : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V},
      @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V f g)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V g f) →
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot α V))
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V g
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot α V)) →
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V g))
    @DomainTheory.NeighbourhoodSystems.ApproximableMap.commuting_least_common_fixed
    @DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement_eq_of_commuting_bot)
  @DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement_iterTwice
end

end DomainTheory.NeighbourhoodSystems.ApproximableMap
end

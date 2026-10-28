module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise_4_10
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise_4_7
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem_4_2

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap
section
variable {α : Type*} {V : NeighborhoodSystem α}
open ApproximableMap
universe u

theorem fix_unique_of_uniform
    (F : ∀ {β : Type u} (W : NeighborhoodSystem β), ApproximableMap W W → W.Element)
    (hfixed : ∀ {β : Type u} (W : NeighborhoodSystem β) (g : ApproximableMap W W),
      g.toElementMap (F W g) = F W g)
    (huniform : ∀ {β γ : Type u} (W₀ : NeighborhoodSystem β) (W₁ : NeighborhoodSystem γ)
      (g₀ : ApproximableMap W₀ W₀) (g₁ : ApproximableMap W₁ W₁) (h : ApproximableMap W₀ W₁),
      h.toElementMap W₀.bot = W₁.bot →
      (∀ x, h.toElementMap (g₀.toElementMap x) = g₁.toElementMap (h.toElementMap x)) →
      h.toElementMap (F W₀ g₀) = F W₁ g₁)
    {α : Type u} (V : NeighborhoodSystem α) (f : ApproximableMap V V) :
    F V f = f.fixElement := by
  have ha : f.toElementMap f.fixElement = f.fixElement := toElementMap_fixElement f

  have hfix' : (relMap f ha).toElementMap (F (relSystem f.fixElement) (relMap f ha)) =
      F (relSystem f.fixElement) (relMap f ha) := hfixed (relSystem f.fixElement) (relMap f ha)

  have huniq : F (relSystem f.fixElement) (relMap f ha) =
      restrict f.fixElement f.fixElement (le_refl _) :=
    relMap_unique_fixed f ha _ hfix'

  have huse := huniform (relSystem f.fixElement) V (relMap f ha) f (inclMap f.fixElement)
    (inclMap_bot f.fixElement) (inclMap_intertwine f ha)
  rw [huniq, inclMap_toElementMap, embed_restrict] at huse
  exact huse.symm
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

theorem iterElem_le_fixElement (f : ApproximableMap V V) (n : ℕ) :
    f.iterElem n ≤ f.fixElement :=
  fun _ hX => ⟨n, (mem_iterElem f n).mp hX⟩

theorem fixElement_uniform {β γ : Type*} {W₀ : NeighborhoodSystem β} {W₁ : NeighborhoodSystem γ}
    (f₀ : ApproximableMap W₀ W₀) (f₁ : ApproximableMap W₁ W₁) (h : ApproximableMap W₀ W₁)
    (hbot : h.toElementMap W₀.bot = W₁.bot)
    (hintw : ∀ x, h.toElementMap (f₀.toElementMap x) = f₁.toElementMap (h.toElementMap x)) :
    h.toElementMap f₀.fixElement = f₁.fixElement := by

  have hiter : ∀ n, h.toElementMap (f₀.iterElem n) = f₁.iterElem n := by
    intro n
    rw [iterElem_eq_iterate f₀ n, iterElem_eq_iterate f₁ n]
    induction n with
    | zero => simpa using hbot
    | succ k ih =>
      rw [Function.iterate_succ', Function.comp_apply, Function.iterate_succ',
        Function.comp_apply, hintw, ih]
  apply le_antisymm
  ·
    rw [fixElement_eq_iSupDirected f₀, toElementMap_iSupDirected]
    apply NeighborhoodSystem.iSupDirected_le
    intro n
    rw [hiter n]
    exact iterElem_le_fixElement f₁ n
  ·
    have hfp : f₁.toElementMap (h.toElementMap f₀.fixElement) = h.toElementMap f₀.fixElement := by
      rw [← hintw f₀.fixElement, toElementMap_fixElement]
    exact fixElement_le_of_toElementMap_le f₁ (le_of_eq hfp)

theorem commuting_least_common_fixed {f g : ApproximableMap V V} (hcomm : f.comp g = g.comp f) :
    ∃ x : V.Element, f.toElementMap x = x ∧ g.toElementMap x = x ∧
      ∀ w : V.Element, f.toElementMap w = w → g.toElementMap w = w → x ≤ w := by
  set a := f.fixElement with ha_def
  have hfa : f.toElementMap a = a := toElementMap_fixElement f

  have ha_le : a ≤ g.toElementMap a := by
    apply fixElement_le_of_toElementMap_le f
    rw [commute_apply hcomm, hfa]
  set x := g.fixAbove ha_le with hx_def
  have hgx : g.toElementMap x = x := fixAbove_isFixed g ha_le
  have hax : a ≤ x := le_fixAbove g ha_le

  have hfix_each : ∀ n, f.toElementMap (g.iterFrom a n) = g.iterFrom a n := by
    intro n
    induction n with
    | zero => rw [iterFrom_zero]; exact hfa
    | succ k ih =>
      rw [iterFrom_succ g a k, commute_apply hcomm, ih]

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

theorem fixElement_eq_of_commuting_bot {f g : ApproximableMap V V} (hcomm : f.comp g = g.comp f)
    (hbot : f.toElementMap V.bot = g.toElementMap V.bot) :
    f.fixElement = g.fixElement := by

  have hshift : ∀ n, g.toElementMap (f.iterElem n) = f.iterElem (n + 1) := by
    intro n
    induction n with
    | zero =>
      rw [iterElem_zero, iterElem_succ, iterElem_zero, ← hbot]
    | succ k ih =>
      rw [iterElem_succ, ← commute_apply hcomm, ih]
      exact (iterElem_succ f (k + 1)).symm

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

  have hshift' : ∀ n, f.toElementMap (g.iterElem n) = g.iterElem (n + 1) := by
    intro n
    induction n with
    | zero =>
      rw [iterElem_zero, iterElem_succ, iterElem_zero, hbot]
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

theorem fixElement_iterTwice (f : ApproximableMap V V) :
    f.fixElement = (f.comp f).fixElement := by
  apply le_antisymm
  ·
    rw [fixElement_eq_iSupDirected f]
    apply NeighborhoodSystem.iSupDirected_le
    intro n
    calc f.iterElem n ≤ f.iterElem (2 * n) := iterElem_mono f (by omega)
      _ = (f.comp f).iterElem n := (comp_self_iterElem f n).symm
      _ ≤ (f.comp f).fixElement := iterElem_le_fixElement (f.comp f) n
  ·
    refine fixElement_le_of_toElementMap_le (f.comp f) (le_of_eq ?_)
    rw [toElementMap_comp, toElementMap_fixElement, toElementMap_fixElement]

end ApproximableMap
end

end DomainTheory.NeighbourhoodSystems
end

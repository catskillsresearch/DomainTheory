module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise_4_10
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem_4_2

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap
section
variable {α : Type*} {V : NeighborhoodSystem α}
open ApproximableMap
universe u
/- concordance: source L2249 EXERCISE 4.11 characterizing the fix combinator -/
/-- **Exercise 4.11 (Scott 1981, PRG-19) — Plotkin's uniqueness.** Any assignment `F` of a
fixed-point operator to every domain satisfying (ii) `F_𝒟(f) = f(F_𝒟(f))` and (iii) the uniformity
law coincides with `fix`: `F_𝒟(f) = fix(f)` for every domain `𝒟` and every `f : 𝒟 → 𝒟`. -/
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
  -- `F` of the restricted map `f'` is a fixed point of `f'` (by (ii))…
  have hfix' : (relMap f ha).toElementMap (F (relSystem f.fixElement) (relMap f ha)) =
      F (relSystem f.fixElement) (relMap f ha) := hfixed (relSystem f.fixElement) (relMap f ha)
  -- …hence it is the unique fixed point `restrict (fix f) (fix f)` of `f'` (Exercise 4.10).
  have huniq : F (relSystem f.fixElement) (relMap f ha) =
      restrict f.fixElement f.fixElement (le_refl _) :=
    relMap_unique_fixed f ha _ hfix'
  -- uniformity along the inclusion `ι` transports `F(f')` to `F(f)`.
  have huse := huniform (relSystem f.fixElement) V (relMap f ha) f (inclMap f.fixElement)
    (inclMap_bot f.fixElement) (inclMap_intertwine f ha)
  rw [huniq, inclMap_toElementMap, embed_restrict] at huse
  exact huse.symm
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- `fⁿ(⊥) ⊑ fix(f)`: every approximant lies below the least fixed point. -/
theorem iterElem_le_fixElement (f : ApproximableMap V V) (n : ℕ) :
    f.iterElem n ≤ f.fixElement :=
  fun _ hX => ⟨n, (mem_iterElem f n).mp hX⟩

/-- **Exercise 4.11(iii) (Scott 1981, PRG-19).** `fix` is *uniform*: if `h(⊥) = ⊥` and
`h ∘ f₀ = f₁ ∘ h`, then `h(fix f₀) = fix f₁`. -/
theorem fixElement_uniform {β γ : Type*} {W₀ : NeighborhoodSystem β} {W₁ : NeighborhoodSystem γ}
    (f₀ : ApproximableMap W₀ W₀) (f₁ : ApproximableMap W₁ W₁) (h : ApproximableMap W₀ W₁)
    (hbot : h.toElementMap W₀.bot = W₁.bot)
    (hintw : ∀ x, h.toElementMap (f₀.toElementMap x) = f₁.toElementMap (h.toElementMap x)) :
    h.toElementMap f₀.fixElement = f₁.fixElement := by
  -- `h` carries the `n`-th approximant of `f₀` to that of `f₁`.
  have hiter : ∀ n, h.toElementMap (f₀.iterElem n) = f₁.iterElem n := by
    intro n
    rw [iterElem_eq_iterate f₀ n, iterElem_eq_iterate f₁ n]
    induction n with
    | zero => simpa using hbot
    | succ k ih =>
      rw [Function.iterate_succ', Function.comp_apply, Function.iterate_succ',
        Function.comp_apply, hintw, ih]
  apply le_antisymm
  · -- `h(fix f₀) = ⊔ₙ h(f₀ⁿ(⊥)) = ⊔ₙ f₁ⁿ(⊥) ⊑ fix f₁`.
    rw [fixElement_eq_iSupDirected f₀, toElementMap_iSupDirected]
    apply NeighborhoodSystem.iSupDirected_le
    intro n
    rw [hiter n]
    exact iterElem_le_fixElement f₁ n
  · -- `h(fix f₀)` is a fixed point of `f₁`, so `fix f₁ ⊑ h(fix f₀)` by minimality.
    have hfp : f₁.toElementMap (h.toElementMap f₀.fixElement) = h.toElementMap f₀.fixElement := by
      rw [← hintw f₀.fixElement, toElementMap_fixElement]
    exact fixElement_le_of_toElementMap_le f₁ (le_of_eq hfp)

end ApproximableMap
end

section
set_option linter.unusedVariables false

theorem example_411.{u_2, u_3, u} : And
  (∀ {β : Type u_2} {γ : Type u_3} {W₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {W₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
    (f₀ : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β W₀ W₀)
    (f₁ : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ γ W₁ W₁)
    (h : @DomainTheory.NeighbourhoodSystems.ApproximableMap β γ W₀ W₁),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ W₁)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ W₀ W₁ h
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot β W₀))
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot γ W₁) →
      (∀ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β W₀),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ W₁)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ W₀ W₁ h
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β β W₀ W₀ f₀ x))
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ γ W₁ W₁ f₁
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ W₀ W₁ h x))) →
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ W₁)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ W₀ W₁ h
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement β W₀ f₀))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement γ W₁ f₁))
  (∀
    (F :
      {β : Type u} →
        (W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β) →
          @DomainTheory.NeighbourhoodSystems.ApproximableMap β β W W →
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β W),
    (∀ {β : Type u} (W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
        (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β W W),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β W)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β β W W g (@F β W g)) (@F β W g)) →
      (∀ {β γ : Type u} (W₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
          (W₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ)
          (g₀ : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β W₀ W₀)
          (g₁ : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ γ W₁ W₁)
          (h : @DomainTheory.NeighbourhoodSystems.ApproximableMap β γ W₀ W₁),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ W₁)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ W₀ W₁ h
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot β W₀))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot γ W₁) →
            (∀ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β W₀),
                @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ W₁)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ W₀ W₁ h
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β β W₀ W₀ g₀ x))
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ γ W₁ W₁ g₁
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ W₀ W₁ h x))) →
              @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ W₁)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ W₀ W₁ h (@F β W₀ g₀))
                (@F γ W₁ g₁)) →
        ∀ {α : Type u} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
          (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (@F α V f)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)) :=
  @And.intro
  (∀ {β : Type u_2} {γ : Type u_3} {W₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {W₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
    (f₀ : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β W₀ W₀)
    (f₁ : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ γ W₁ W₁)
    (h : @DomainTheory.NeighbourhoodSystems.ApproximableMap β γ W₀ W₁),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ W₁)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ W₀ W₁ h
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot β W₀))
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot γ W₁) →
      (∀ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β W₀),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ W₁)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ W₀ W₁ h
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β β W₀ W₀ f₀ x))
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ γ W₁ W₁ f₁
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ W₀ W₁ h x))) →
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ W₁)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ W₀ W₁ h
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement β W₀ f₀))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement γ W₁ f₁))
  (∀
    (F :
      {β : Type u} →
        (W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β) →
          @DomainTheory.NeighbourhoodSystems.ApproximableMap β β W W →
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β W),
    (∀ {β : Type u} (W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
        (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β W W),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β W)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β β W W g (@F β W g)) (@F β W g)) →
      (∀ {β γ : Type u} (W₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
          (W₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ)
          (g₀ : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β W₀ W₀)
          (g₁ : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ γ W₁ W₁)
          (h : @DomainTheory.NeighbourhoodSystems.ApproximableMap β γ W₀ W₁),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ W₁)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ W₀ W₁ h
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot β W₀))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot γ W₁) →
            (∀ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β W₀),
                @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ W₁)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ W₀ W₁ h
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β β W₀ W₀ g₀ x))
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ γ W₁ W₁ g₁
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ W₀ W₁ h x))) →
              @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ W₁)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ W₀ W₁ h (@F β W₀ g₀))
                (@F γ W₁ g₁)) →
        ∀ {α : Type u} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
          (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (@F α V f)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))
  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement_uniform)
  DomainTheory.NeighbourhoodSystems.fix_unique_of_uniform
end

end DomainTheory.NeighbourhoodSystems
end


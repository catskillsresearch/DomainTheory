module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise407
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise411.inclMap
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise411.inclMap_toElementMap
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise411.inclMap_bot
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise411.inclMap_intertwine

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.relMap_unique_fixed
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}


open ApproximableMap

universe u

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

end DomainTheory.NeighbourhoodSystems

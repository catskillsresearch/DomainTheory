module
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_5

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6
@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem
variable {α β γ δ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {V₂ : NeighborhoodSystem γ}
open ApproximableMap
/- concordance: source L1036 PROPOSITION 3.4 pairing and projections -/
/-- **Proposition 3.4(i) (Scott 1981, PRG-19).** `p₀ ∘ ⟨f, g⟩ = f`. -/
theorem proj₀_comp_paired (f : ApproximableMap V₂ V₀) (g : ApproximableMap V₂ V₁) :
    (proj₀ V₀ V₁).comp (paired f g) = f := by
  apply ext_of_toElementMap
  intro w
  rw [toElementMap_comp, toElementMap_paired, toElementMap_proj₀, fst_pair]

/-- **Proposition 3.4(i) (Scott 1981, PRG-19).** `p₁ ∘ ⟨f, g⟩ = g`. -/
theorem proj₁_comp_paired (f : ApproximableMap V₂ V₀) (g : ApproximableMap V₂ V₁) :
    (proj₁ V₀ V₁).comp (paired f g) = g := by
  apply ext_of_toElementMap
  intro w
  rw [toElementMap_comp, toElementMap_paired, toElementMap_proj₁, snd_pair]

/-- **Theorem 3.5 (elementwise) (Scott 1981, PRG-19).** The two-variable elementwise map of
`toMap₂ f` is `f` evaluated at the pairing: `(toMap₂ f)(x, y) = f(⟨x, y⟩)`. -/
theorem toElementMap₂_toMap₂ (f : ApproximableMap (prod V₀ V₁) V₂) (x : V₀.Element) (y : V₁.Element) :
    (toMap₂ f).toElementMap₂ x y = f.toElementMap (pair x y) := by
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨X, Y, hX, hY, hrel⟩
    exact ⟨prodNbhd X Y, ⟨X, Y, hX, hY, rfl⟩, hrel⟩
  · rintro ⟨W, ⟨X, Y, hX, hY, rfl⟩, hrel⟩
    exact ⟨X, Y, hX, hY, hrel⟩
end

end DomainTheory.NeighbourhoodSystems
end

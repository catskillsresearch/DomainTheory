module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_4
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
variable {V₃ : NeighborhoodSystem δ}
/- concordance: source L1129 PROPOSITION 3.7 closure under substitution -/
/-- **Proposition 3.7 (Scott 1981, PRG-19).** Multivariate approximable functions are closed under
substitution: substituting approximable maps `a, b : 𝒟₃ → 𝒟ᵢ` into a two-variable approximable map
`F : 𝒟₀ × 𝒟₁ → 𝒟₂` yields the approximable map `F ∘ ⟨a, b⟩`, whose value is `F(a(w), b(w))`. The
building blocks are exactly Definition 3.3's `paired` and Theorem 2.5's `comp`. -/
theorem substitution_toElementMap (F : ApproximableMap (prod V₀ V₁) V₂)
    (a : ApproximableMap V₃ V₀) (b : ApproximableMap V₃ V₁) (w : V₃.Element) :
    (F.comp (paired a b)).toElementMap w
      = (toMap₂ F).toElementMap₂ (a.toElementMap w) (b.toElementMap w) := by
  rw [toElementMap_comp, toElementMap_paired, toElementMap₂_toMap₂]
end

end DomainTheory.NeighbourhoodSystems
end


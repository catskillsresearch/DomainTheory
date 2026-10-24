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

/-- **Proposition 3.4 (Scott 1981, PRG-19).** Pairing and projections: `p₀ ∘ ⟨f, g⟩ = f`,
`p₁ ∘ ⟨f, g⟩ = g`, `h = ⟨p₀ ∘ h, p₁ ∘ h⟩`, and `⟨f, g⟩(w) = ⟨f(w), g(w)⟩`. -/
theorem proposition_3_4 :
    (∀ (f : ApproximableMap V₂ V₀) (g : ApproximableMap V₂ V₁),
      (proj₀ V₀ V₁).comp (paired f g) = f ∧ (proj₁ V₀ V₁).comp (paired f g) = g) ∧
    (∀ (h : ApproximableMap V₂ (prod V₀ V₁)),
      paired ((proj₀ V₀ V₁).comp h) ((proj₁ V₀ V₁).comp h) = h) ∧
    (∀ (f : ApproximableMap V₂ V₀) (g : ApproximableMap V₂ V₁) (w : V₂.Element),
      (paired f g).toElementMap w = pair (f.toElementMap w) (g.toElementMap w)) :=
  ⟨fun f g => ⟨proj₀_comp_paired f g, proj₁_comp_paired f g⟩, paired_proj, toElementMap_paired⟩

end
end DomainTheory.NeighbourhoodSystems
end
